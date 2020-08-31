Pod::Spec.new do |spec|

  spec.name         = "ed25519"
  spec.version      = "1.0.0"
  spec.summary      = "ed25519."
  spec.homepage     = "https://github.com/Bytom/Bycoin.iOS"
  spec.license      = "MIT"
  spec.author       = 'SuperY'

  spec.swift_version = '5'
  spec.module_name = 'ed25519'
  spec.platform     = :ios, "10.0"
  spec.ios.deployment_target = "10.0"
  spec.source       = { :git => "https://github.com/SuperY/ed25519.git", :tag => "#{spec.version}" }

  spec.source_files = "ed25519/**/*.{h,swift}"
  spec.public_header_files = "ed25519/**/*.h"

  spec.pod_target_xcconfig = {
    'SWIFT_OPTIMIZATION_LEVEL' => '-Owholemodule'
  }

end

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t716 = true := by
  decide +kernel

theorem tot716 : totK PA10K2 A10K2.t716 = [0, 0, 295744337488, 1179154894064, 1878644137331, 1081707916174, 183043125638, 6034215561, 0, 0] := by
  decide +kernel

theorem rows717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t717 = true := by
  decide +kernel

theorem tot717 : totK PA10K2 A10K2.t717 = [0, 0, 545047435466, 1929109577558, 1799961074573, 430699403467, 26386655430, 0, 0, 0] := by
  decide +kernel

theorem rows718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t718 = true := by
  decide +kernel

theorem tot718 : totK PA10K2 A10K2.t718 = [0, 0, 0, 953414251035, 2363702905706, 1191029438441, 112069967990, 0, 0, 0] := by
  decide +kernel

theorem rows719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t719 = true := by
  decide +kernel

theorem tot719 : totK PA10K2 A10K2.t719 = [0, 0, 0, 461461694571, 1856473487173, 1755925841403, 462070973905, 31193230065, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

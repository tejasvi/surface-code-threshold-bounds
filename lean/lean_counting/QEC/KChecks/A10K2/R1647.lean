import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6588 = true := by
  decide +kernel

theorem tot6588 : totK PA10K2 A10K2.t6588 = [0, 0, 277969155514, 1235415914089, 1981113563831, 1183840259875, 231896155551, 6962742351, 0, 0] := by
  decide +kernel

theorem rows6589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6589 = true := by
  decide +kernel

theorem tot6589 : totK PA10K2 A10K2.t6589 = [0, 0, 282576922599, 1505333623670, 2154548720417, 747582568797, 57593161139, 0, 0, 0] := by
  decide +kernel

theorem rows6590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6590 = true := by
  decide +kernel

theorem tot6590 : totK PA10K2 A10K2.t6590 = [0, 0, 331872270827, 1273476140663, 1881695237429, 1033360683541, 160973900439, 5460492893, 0, 0] := by
  decide +kernel

theorem rows6591 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6591 = true := by
  decide +kernel

theorem tot6591 : totK PA10K2 A10K2.t6591 = [0, 0, 434887155920, 1762400462745, 2015253724365, 644107385242, 40441619481, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

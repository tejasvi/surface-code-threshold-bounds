import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6288 = true := by
  decide +kernel

theorem tot6288 : totK PA10K2 A10K2.t6288 = [219385222726, 1115865174192, 2012414548611, 1403136675674, 303129226440, 20340910120, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6289 = true := by
  decide +kernel

theorem tot6289 : totK PA10K2 A10K2.t6289 = [171985178779, 883607782602, 1843169459265, 1545168433590, 330274043750, 11427838733, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6290 = true := by
  decide +kernel

theorem tot6290 : totK PA10K2 A10K2.t6290 = [459358432056, 1697452287913, 1886692414433, 646839800706, 52232171148, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6291 = true := by
  decide +kernel

theorem tot6291 : totK PA10K2 A10K2.t6291 = [112111361307, 1208751340077, 2244113971937, 1029915770651, 86873488790, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

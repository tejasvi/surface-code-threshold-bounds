import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t736 = true := by
  decide +kernel

theorem tot736 : totK PA10K2 A10K2.t736 = [0, 599813020445, 1875771494344, 1777766543295, 494075195696, 31608797364, 0, 0, 0, 0] := by
  decide +kernel

theorem rows737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t737 = true := by
  decide +kernel

theorem tot737 : totK PA10K2 A10K2.t737 = [0, 39814905974, 1078650617374, 2328081370042, 1102839865192, 91903180186, 0, 0, 0, 0] := by
  decide +kernel

theorem rows738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t738 = true := by
  decide +kernel

theorem tot738 : totK PA10K2 A10K2.t738 = [0, 483788266945, 1665613312263, 1826901840981, 796246258867, 134266913175, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t739 = true := by
  decide +kernel

theorem tot739 : totK PA10K2 A10K2.t739 = [252491579350, 918628875683, 1574263600123, 1622134004729, 614413924970, 50491866487, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

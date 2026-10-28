import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t752 = true := by
  decide +kernel

theorem tot752 : totK PA10K2 A10K2.t752 = [558482342224, 1899916075985, 1920242612745, 621634455163, 58879853381, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t753 = true := by
  decide +kernel

theorem tot753 : totK PA10K2 A10K2.t753 = [0, 716879141669, 2168589080602, 1708106223050, 340404559935, 19734769798, 0, 0, 0, 0] := by
  decide +kernel

theorem rows754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t754 = true := by
  decide +kernel

theorem tot754 : totK PA10K2 A10K2.t754 = [534468218564, 1840593165215, 1902614409034, 647772667279, 64108529215, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t755 = true := by
  decide +kernel

theorem tot755 : totK PA10K2 A10K2.t755 = [327737319032, 1501014675106, 2137326136579, 911025889743, 82661194815, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

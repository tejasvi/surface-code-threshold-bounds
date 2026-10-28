import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2592 = true := by
  decide +kernel

theorem tot2592 : totK PA10K2 A10K2.t2592 = [568096137437, 1952939536278, 1809322558224, 456467075403, 26521581199, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2593 = true := by
  decide +kernel

theorem tot2593 : totK PA10K2 A10K2.t2593 = [0, 944301052465, 2382068131981, 1266226031690, 113943173993, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2594 = true := by
  decide +kernel

theorem tot2594 : totK PA10K2 A10K2.t2594 = [0, 424970032338, 1772279217976, 1869976327669, 525227725495, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2595 = true := by
  decide +kernel

theorem tot2595 : totK PA10K2 A10K2.t2595 = [0, 603711135755, 1952633307561, 1750309735388, 391372241032, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

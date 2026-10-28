import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11984 = true := by
  decide +kernel

theorem tot11984 : totK PD2M8K2 D2M8K2.t11984 = [113317089915, 432313048793, 322665777215, 27464650445, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11985 = true := by
  decide +kernel

theorem tot11985 : totK PD2M8K2 D2M8K2.t11985 = [0, 207617694285, 481977780079, 189019494994, 9668735432, 0, 0, 0] := by
  decide +kernel

theorem rows11986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11986 = true := by
  decide +kernel

theorem tot11986 : totK PD2M8K2 D2M8K2.t11986 = [85741851239, 326454851917, 367255867653, 100438590684, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows11987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11987 = true := by
  decide +kernel

theorem tot11987 : totK PD2M8K2 D2M8K2.t11987 = [172648977113, 447094274735, 269424602310, 28740480200, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

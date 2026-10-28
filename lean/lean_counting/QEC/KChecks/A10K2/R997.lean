import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3988 = true := by
  decide +kernel

theorem tot3988 : totK PA10K2 A10K2.t3988 = [0, 0, 252958442976, 608847853352, 840875644354, 1641961508514, 1087564386613, 189164816705, 6239673734, 0] := by
  decide +kernel

theorem rows3989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3989 = true := by
  decide +kernel

theorem tot3989 : totK PA10K2 A10K2.t3989 = [0, 0, 303663418211, 1543815189487, 2231209052764, 898940295360, 77640018351, 0, 0, 0] := by
  decide +kernel

theorem rows3990 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3990 = true := by
  decide +kernel

theorem tot3990 : totK PA10K2 A10K2.t3990 = [0, 0, 308574149355, 1240862596949, 1952499706143, 1276365223409, 214297920302, 7007974415, 0, 0] := by
  decide +kernel

theorem rows3991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3991 = true := by
  decide +kernel

theorem tot3991 : totK PA10K2 A10K2.t3991 = [0, 0, 495188181108, 1869212338770, 1997036975051, 567103558746, 31908368213, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

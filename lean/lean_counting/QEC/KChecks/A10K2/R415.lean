import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1660 = true := by
  decide +kernel

theorem tot1660 : totK PA10K2 A10K2.t1660 = [0, 0, 188521259194, 991778565075, 1956747046914, 1365031901836, 298519597310, 25565504801, 0, 0] := by
  decide +kernel

theorem rows1661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1661 = true := by
  decide +kernel

theorem tot1661 : totK PA10K2 A10K2.t1661 = [0, 0, 202308092638, 1180792974778, 2064748735807, 1118999495944, 170813976107, 5517381808, 0, 0] := by
  decide +kernel

theorem rows1662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1662 = true := by
  decide +kernel

theorem tot1662 : totK PA10K2 A10K2.t1662 = [0, 0, 577819886779, 1908617124276, 1730195062406, 457777740043, 31936107789, 0, 0, 0] := by
  decide +kernel

theorem rows1663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1663 = true := by
  decide +kernel

theorem tot1663 : totK PA10K2 A10K2.t1663 = [0, 0, 0, 966886429861, 2458033510437, 1138709014326, 83755589175, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1364 = true := by
  decide +kernel

theorem tot1364 : totK PD2M8K2 D2M8K2.t1364 = [0, 104846222363, 395861367361, 353600449825, 48304019825, 0, 0, 0] := by
  decide +kernel

theorem rows1365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1365 = true := by
  decide +kernel

theorem tot1365 : totK PD2M8K2 D2M8K2.t1365 = [0, 184389666054, 458154103009, 223270468995, 16972168943, 0, 0, 0] := by
  decide +kernel

theorem rows1366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1366 = true := by
  decide +kernel

theorem tot1366 : totK PD2M8K2 D2M8K2.t1366 = [0, 51471199552, 340447714393, 416108659501, 72524393882, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1367 = true := by
  decide +kernel

theorem tot1367 : totK PD2M8K2 D2M8K2.t1367 = [0, 109419402852, 418797649023, 346730971753, 31266694764, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1564 = true := by
  decide +kernel

theorem tot1564 : totK PD2M8K2 D2M8K2.t1564 = [0, 0, 0, 281242190771, 472594575469, 110555639445, 2305904642, 0] := by
  decide +kernel

theorem rows1565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1565 = true := by
  decide +kernel

theorem tot1565 : totK PD2M8K2 D2M8K2.t1565 = [0, 0, 58987240919, 250060882902, 381180311978, 138098364734, 10710292732, 0] := by
  decide +kernel

theorem rows1566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1566 = true := by
  decide +kernel

theorem tot1566 : totK PD2M8K2 D2M8K2.t1566 = [0, 0, 190961250024, 479564560916, 203418799360, 6700120827, 0, 0] := by
  decide +kernel

theorem rows1567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1567 = true := by
  decide +kernel

theorem tot1567 : totK PD2M8K2 D2M8K2.t1567 = [0, 0, 157159178082, 465666980530, 235264122882, 13086486553, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

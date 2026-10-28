import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t380 = true := by
  decide +kernel

theorem tot380 : totK PD2M8K2 D2M8K2.t380 = [0, 155971048597, 465167871576, 237586944191, 13144444366, 0, 0, 0] := by
  decide +kernel

theorem rows381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t381 = true := by
  decide +kernel

theorem tot381 : totK PD2M8K2 D2M8K2.t381 = [0, 0, 304715144457, 468460993324, 76533227365, 1021600638, 0, 0] := by
  decide +kernel

theorem rows382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t382 = true := by
  decide +kernel

theorem tot382 : totK PD2M8K2 D2M8K2.t382 = [0, 104239363842, 353555634310, 318499017132, 76305736775, 3552795014, 0, 0] := by
  decide +kernel

theorem rows383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t383 = true := by
  decide +kernel

theorem tot383 : totK PD2M8K2 D2M8K2.t383 = [0, 171924110589, 444733846184, 257435758940, 25338317800, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

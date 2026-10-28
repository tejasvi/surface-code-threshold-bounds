import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1392 = true := by
  decide +kernel

theorem tot1392 : totK PD2M8K2 D2M8K2.t1392 = [0, 120880495730, 359925090913, 347371817161, 75411256329, 1189976475, 0, 0] := by
  decide +kernel

theorem rows1393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1393 = true := by
  decide +kernel

theorem tot1393 : totK PD2M8K2 D2M8K2.t1393 = [0, 158229995465, 441601758948, 281325987531, 30469665423, 0, 0, 0] := by
  decide +kernel

theorem rows1394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1394 = true := by
  decide +kernel

theorem tot1394 : totK PD2M8K2 D2M8K2.t1394 = [0, 124404585768, 421122566300, 317260425910, 36605225424, 0, 0, 0] := by
  decide +kernel

theorem rows1395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1395 = true := by
  decide +kernel

theorem tot1395 : totK PD2M8K2 D2M8K2.t1395 = [0, 0, 229014531361, 479142997790, 176881276364, 7947699043, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7456 = true := by
  decide +kernel

theorem tot7456 : totK PD2M8K2 D2M8K2.t7456 = [0, 180187839875, 458014414030, 251338964974, 17034006105, 0, 0, 0] := by
  decide +kernel

theorem rows7457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7457 = true := by
  decide +kernel

theorem tot7457 : totK PD2M8K2 D2M8K2.t7457 = [0, 0, 285173731139, 497726363102, 117836155220, 1268739303, 0, 0] := by
  decide +kernel

theorem rows7458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7458 = true := by
  decide +kernel

theorem tot7458 : totK PD2M8K2 D2M8K2.t7458 = [0, 0, 203404614879, 480093645145, 182992567513, 7442000727, 0, 0] := by
  decide +kernel

theorem rows7459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7459 = true := by
  decide +kernel

theorem tot7459 : totK PD2M8K2 D2M8K2.t7459 = [0, 0, 188591122039, 470401572611, 217639977551, 14707859566, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

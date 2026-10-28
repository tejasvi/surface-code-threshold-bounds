import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12748 = true := by
  decide +kernel

theorem tot12748 : totK PD2M8K2 D2M8K2.t12748 = [0, 0, 104067171422, 356055120661, 348837042322, 76961178548, 1186940923, 0] := by
  decide +kernel

theorem rows12749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12749 = true := by
  decide +kernel

theorem tot12749 : totK PD2M8K2 D2M8K2.t12749 = [0, 0, 172044566301, 439218728340, 271268925303, 30307792245, 0, 0] := by
  decide +kernel

theorem rows12750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12750 = true := by
  decide +kernel

theorem tot12750 : totK PD2M8K2 D2M8K2.t12750 = [0, 0, 143160765898, 455304258691, 274114793998, 15950332135, 0, 0] := by
  decide +kernel

theorem rows12751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12751 = true := by
  decide +kernel

theorem tot12751 : totK PD2M8K2 D2M8K2.t12751 = [0, 0, 0, 331509594084, 514812100977, 70153779911, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

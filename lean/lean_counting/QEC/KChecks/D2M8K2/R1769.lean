import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7076 = true := by
  decide +kernel

theorem tot7076 : totK PD2M8K2 D2M8K2.t7076 = [0, 0, 218505940150, 507075572094, 167134171351, 2530668022, 0, 0] := by
  decide +kernel

theorem rows7077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7077 = true := by
  decide +kernel

theorem tot7077 : totK PD2M8K2 D2M8K2.t7077 = [0, 0, 169277317188, 460136976088, 213292642960, 12367370283, 0, 0] := by
  decide +kernel

theorem rows7078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7078 = true := by
  decide +kernel

theorem tot7078 : totK PD2M8K2 D2M8K2.t7078 = [0, 0, 187058118837, 476564588085, 208172136670, 10372644569, 0, 0] := by
  decide +kernel

theorem rows7079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7079 = true := by
  decide +kernel

theorem tot7079 : totK PD2M8K2 D2M8K2.t7079 = [0, 0, 181776582035, 443462398964, 215178716540, 16861767938, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

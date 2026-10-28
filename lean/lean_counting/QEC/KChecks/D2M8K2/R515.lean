import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2060 = true := by
  decide +kernel

theorem tot2060 : totK PD2M8K2 D2M8K2.t2060 = [0, 0, 67625271801, 358023389995, 361391069097, 63763375733, 1138244013, 0] := by
  decide +kernel

theorem rows2061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2061 = true := by
  decide +kernel

theorem tot2061 : totK PD2M8K2 D2M8K2.t2061 = [0, 0, 90869407961, 415122837495, 346251289905, 33943025390, 0, 0] := by
  decide +kernel

theorem rows2062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2062 = true := by
  decide +kernel

theorem tot2062 : totK PD2M8K2 D2M8K2.t2062 = [0, 0, 166321843275, 466619304433, 247828092115, 14087263160, 0, 0] := by
  decide +kernel

theorem rows2063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2063 = true := by
  decide +kernel

theorem tot2063 : totK PD2M8K2 D2M8K2.t2063 = [0, 0, 209508695921, 492261698282, 196112659759, 5340457792, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

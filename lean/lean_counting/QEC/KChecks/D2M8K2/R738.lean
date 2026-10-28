import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2952 = true := by
  decide +kernel

theorem tot2952 : totK PD2M8K2 D2M8K2.t2952 = [0, 70333055629, 337645582742, 393373829160, 78252057818, 1310285577, 0, 0] := by
  decide +kernel

theorem rows2953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2953 = true := by
  decide +kernel

theorem tot2953 : totK PD2M8K2 D2M8K2.t2953 = [0, 84843550641, 372014394145, 407131384199, 41533919791, 0, 0, 0] := by
  decide +kernel

theorem rows2954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2954 = true := by
  decide +kernel

theorem tot2954 : totK PD2M8K2 D2M8K2.t2954 = [0, 167895751414, 442877097881, 279813456423, 28529815567, 0, 0, 0] := by
  decide +kernel

theorem rows2955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2955 = true := by
  decide +kernel

theorem tot2955 : totK PD2M8K2 D2M8K2.t2955 = [0, 167190446321, 489703352369, 256859096562, 11713192438, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

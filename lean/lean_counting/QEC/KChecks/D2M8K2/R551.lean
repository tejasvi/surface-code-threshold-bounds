import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2204 = true := by
  decide +kernel

theorem tot2204 : totK PD2M8K2 D2M8K2.t2204 = [0, 175595421913, 438705034637, 269782051435, 24282010842, 0, 0, 0] := by
  decide +kernel

theorem rows2205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2205 = true := by
  decide +kernel

theorem tot2205 : totK PD2M8K2 D2M8K2.t2205 = [0, 119946469230, 430472977518, 317741419925, 35880718840, 0, 0, 0] := by
  decide +kernel

theorem rows2206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2206 = true := by
  decide +kernel

theorem tot2206 : totK PD2M8K2 D2M8K2.t2206 = [0, 0, 153588090908, 442357580683, 275370091851, 26664167796, 0, 0] := by
  decide +kernel

theorem rows2207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2207 = true := by
  decide +kernel

theorem tot2207 : totK PD2M8K2 D2M8K2.t2207 = [0, 50460163317, 209350556669, 424968178610, 200882965355, 6793297366, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

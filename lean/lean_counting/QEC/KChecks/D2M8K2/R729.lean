import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2916 = true := by
  decide +kernel

theorem tot2916 : totK PD2M8K2 D2M8K2.t2916 = [0, 292750594666, 516680127953, 101061744522, 1069412848, 0, 0, 0] := by
  decide +kernel

theorem rows2917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2917 = true := by
  decide +kernel

theorem tot2917 : totK PD2M8K2 D2M8K2.t2917 = [0, 176189214897, 461534291840, 215850913705, 12554737991, 0, 0, 0] := by
  decide +kernel

theorem rows2918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2918 = true := by
  decide +kernel

theorem tot2918 : totK PD2M8K2 D2M8K2.t2918 = [0, 196828358161, 472315482511, 202071558141, 12421902774, 0, 0, 0] := by
  decide +kernel

theorem rows2919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2919 = true := by
  decide +kernel

theorem tot2919 : totK PD2M8K2 D2M8K2.t2919 = [0, 0, 308603422585, 460184502871, 75337031653, 1138244013, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

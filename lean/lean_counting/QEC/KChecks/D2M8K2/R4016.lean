import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16064 = true := by
  decide +kernel

theorem tot16064 : totK PD2M8K2 D2M8K2.t16064 = [0, 0, 249622983325, 512172225907, 136427560066, 2309606161, 0, 0] := by
  decide +kernel

theorem rows16065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16065 = true := by
  decide +kernel

theorem tot16065 : totK PD2M8K2 D2M8K2.t16065 = [0, 75698288311, 271387803319, 392607966784, 130522308396, 6505865812, 0, 0] := by
  decide +kernel

theorem rows16066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16066 = true := by
  decide +kernel

theorem tot16066 : totK PD2M8K2 D2M8K2.t16066 = [0, 168723317857, 471008383705, 255377740063, 20018134242, 0, 0, 0] := by
  decide +kernel

theorem rows16067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16067 = true := by
  decide +kernel

theorem tot16067 : totK PD2M8K2 D2M8K2.t16067 = [0, 163655033574, 454219016706, 250837698764, 16297494506, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

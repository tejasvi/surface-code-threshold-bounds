import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12920 = true := by
  decide +kernel

theorem tot12920 : totK PD2M8K2 D2M8K2.t12920 = [0, 0, 209157715950, 486304819993, 205433154020, 7994456143, 0, 0] := by
  decide +kernel

theorem rows12921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12921 = true := by
  decide +kernel

theorem tot12921 : totK PD2M8K2 D2M8K2.t12921 = [0, 70538324455, 240563425446, 386902116039, 184275684419, 8214505460, 0, 0] := by
  decide +kernel

theorem rows12922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12922 = true := by
  decide +kernel

theorem tot12922 : totK PD2M8K2 D2M8K2.t12922 = [0, 182823446433, 456049335209, 265018775157, 24536116903, 0, 0, 0] := by
  decide +kernel

theorem rows12923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12923 = true := by
  decide +kernel

theorem tot12923 : totK PD2M8K2 D2M8K2.t12923 = [0, 171653799542, 471686951092, 238855853881, 12446270221, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

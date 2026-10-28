import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14212 = true := by
  decide +kernel

theorem tot14212 : totK PD2M8K2 D2M8K2.t14212 = [0, 190807454766, 476929700540, 216957717700, 14692590779, 0, 0, 0] := by
  decide +kernel

theorem rows14213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14213 = true := by
  decide +kernel

theorem tot14213 : totK PD2M8K2 D2M8K2.t14213 = [0, 168151637556, 460963926634, 211370264181, 10735115630, 0, 0, 0] := by
  decide +kernel

theorem rows14214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14214 = true := by
  decide +kernel

theorem tot14214 : totK PD2M8K2 D2M8K2.t14214 = [0, 86379301702, 350815193480, 354752516029, 66373920131, 1206465782, 0, 0] := by
  decide +kernel

theorem rows14215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14215 = true := by
  decide +kernel

theorem tot14215 : totK PD2M8K2 D2M8K2.t14215 = [0, 40663345568, 373183132246, 420551160508, 41715777069, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

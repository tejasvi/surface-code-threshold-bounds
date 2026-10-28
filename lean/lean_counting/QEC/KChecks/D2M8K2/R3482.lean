import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13928 = true := by
  decide +kernel

theorem tot13928 : totK PD2M8K2 D2M8K2.t13928 = [89381903860, 359824985781, 378299370675, 75912651931, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows13929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13929 = true := by
  decide +kernel

theorem tot13929 : totK PD2M8K2 D2M8K2.t13929 = [0, 226041691250, 482755790952, 171083847290, 9459556122, 0, 0, 0] := by
  decide +kernel

theorem rows13930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13930 = true := by
  decide +kernel

theorem tot13930 : totK PD2M8K2 D2M8K2.t13930 = [161849979831, 415941240406, 277083823808, 57358951934, 2426968038, 0, 0, 0] := by
  decide +kernel

theorem rows13931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13931 = true := by
  decide +kernel

theorem tot13931 : totK PD2M8K2 D2M8K2.t13931 = [168807535706, 443039311230, 278697162239, 29952589139, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

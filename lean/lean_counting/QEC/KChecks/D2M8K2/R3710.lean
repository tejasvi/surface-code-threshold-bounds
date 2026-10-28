import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14840 = true := by
  decide +kernel

theorem tot14840 : totK PD2M8K2 D2M8K2.t14840 = [0, 272372489119, 511619868062, 109423741703, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows14841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14841 = true := by
  decide +kernel

theorem tot14841 : totK PD2M8K2 D2M8K2.t14841 = [162708114747, 436020477813, 299078420087, 36935652971, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14842 = true := by
  decide +kernel

theorem tot14842 : totK PD2M8K2 D2M8K2.t14842 = [167519636022, 468742762865, 247858840493, 16199876001, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14843 = true := by
  decide +kernel

theorem tot14843 : totK PD2M8K2 D2M8K2.t14843 = [88459214294, 320734352282, 360147847619, 132711806070, 15848128199, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

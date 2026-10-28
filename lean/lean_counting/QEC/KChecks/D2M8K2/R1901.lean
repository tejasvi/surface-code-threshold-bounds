import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7604 = true := by
  decide +kernel

theorem tot7604 : totK PD2M8K2 D2M8K2.t7604 = [0, 0, 92859452576, 423524135287, 336925209071, 31263376485, 0, 0] := by
  decide +kernel

theorem rows7605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7605 = true := by
  decide +kernel

theorem tot7605 : totK PD2M8K2 D2M8K2.t7605 = [0, 0, 165754437816, 449019679239, 259024322386, 23594851847, 0, 0] := by
  decide +kernel

theorem rows7606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7606 = true := by
  decide +kernel

theorem tot7606 : totK PD2M8K2 D2M8K2.t7606 = [0, 0, 194876180562, 484215482838, 225085870567, 9645302066, 0, 0] := by
  decide +kernel

theorem rows7607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7607 = true := by
  decide +kernel

theorem tot7607 : totK PD2M8K2 D2M8K2.t7607 = [0, 0, 191387557057, 480058217725, 217637828985, 11051716772, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

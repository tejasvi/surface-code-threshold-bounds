import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12212 = true := by
  decide +kernel

theorem tot12212 : totK PD2M8K2 D2M8K2.t12212 = [0, 231445253359, 483093207271, 166072707076, 9473607896, 0, 0, 0] := by
  decide +kernel

theorem rows12213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12213 = true := by
  decide +kernel

theorem tot12213 : totK PD2M8K2 D2M8K2.t12213 = [160882570615, 410472200547, 272735641769, 61456880614, 2566665356, 0, 0, 0] := by
  decide +kernel

theorem rows12214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12214 = true := by
  decide +kernel

theorem tot12214 : totK PD2M8K2 D2M8K2.t12214 = [172659237846, 436221985323, 272782186114, 30498142501, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12215 = true := by
  decide +kernel

theorem tot12215 : totK PD2M8K2 D2M8K2.t12215 = [91681601894, 387432552394, 347238107891, 55085069851, 1096156699, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

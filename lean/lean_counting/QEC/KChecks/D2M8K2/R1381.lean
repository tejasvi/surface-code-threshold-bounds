import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5524 = true := by
  decide +kernel

theorem tot5524 : totK PD2M8K2 D2M8K2.t5524 = [0, 208363334450, 472767084640, 178750198842, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows5525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5525 = true := by
  decide +kernel

theorem tot5525 : totK PD2M8K2 D2M8K2.t5525 = [0, 183963829093, 478282957222, 220842229638, 14707859566, 0, 0, 0] := by
  decide +kernel

theorem rows5526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5526 = true := by
  decide +kernel

theorem tot5526 : totK PD2M8K2 D2M8K2.t5526 = [0, 181220975655, 455818800052, 222996380079, 16632994142, 0, 0, 0] := by
  decide +kernel

theorem rows5527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5527 = true := by
  decide +kernel

theorem tot5527 : totK PD2M8K2 D2M8K2.t5527 = [0, 163490325283, 457261224661, 243467677747, 18471174381, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

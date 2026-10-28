import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1020 = true := by
  decide +kernel

theorem tot1020 : totK PD2M8K2 D2M8K2.t1020 = [0, 0, 240616781638, 492404206476, 139237614762, 2318623666, 0, 0] := by
  decide +kernel

theorem rows1021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1021 = true := by
  decide +kernel

theorem tot1021 : totK PD2M8K2 D2M8K2.t1021 = [0, 76470241695, 275527312513, 360994840321, 131560056102, 10786826731, 0, 0] := by
  decide +kernel

theorem rows1022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1022 = true := by
  decide +kernel

theorem tot1022 : totK PD2M8K2 D2M8K2.t1022 = [0, 163258724509, 471838645320, 237888182100, 12084350913, 0, 0, 0] := by
  decide +kernel

theorem rows1023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1023 = true := by
  decide +kernel

theorem tot1023 : totK PD2M8K2 D2M8K2.t1023 = [0, 179935757967, 478358668144, 231315769048, 12163338161, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

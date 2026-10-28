import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6748 = true := by
  decide +kernel

theorem tot6748 : totK PD2M8K2 D2M8K2.t6748 = [0, 0, 279941954503, 468808811520, 107891435304, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6749 = true := by
  decide +kernel

theorem tot6749 : totK PD2M8K2 D2M8K2.t6749 = [0, 120475736232, 422484566424, 311292737560, 30799458298, 0, 0, 0] := by
  decide +kernel

theorem rows6750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6750 = true := by
  decide +kernel

theorem tot6750 : totK PD2M8K2 D2M8K2.t6750 = [0, 194531686601, 470728602165, 217744157864, 12534922032, 0, 0, 0] := by
  decide +kernel

theorem rows6751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6751 = true := by
  decide +kernel

theorem tot6751 : totK PD2M8K2 D2M8K2.t6751 = [0, 180899080173, 474848729874, 220409824688, 12593797338, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

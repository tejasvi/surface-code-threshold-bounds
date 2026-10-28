import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11556 = true := by
  decide +kernel

theorem tot11556 : totK PD2M8K2 D2M8K2.t11556 = [0, 0, 178176977009, 462873211260, 246866344399, 11596035270, 0, 0] := by
  decide +kernel

theorem rows11557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11557 = true := by
  decide +kernel

theorem tot11557 : totK PD2M8K2 D2M8K2.t11557 = [0, 0, 0, 290249757475, 492881481612, 92674145437, 1229550402, 0] := by
  decide +kernel

theorem rows11558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11558 = true := by
  decide +kernel

theorem tot11558 : totK PD2M8K2 D2M8K2.t11558 = [65745007336, 91416121127, 11423009356, 143593630179, 393497652979, 169144195257, 8304201444, 0] := by
  decide +kernel

theorem rows11559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11559 = true := by
  decide +kernel

theorem tot11559 : totK PD2M8K2 D2M8K2.t11559 = [192040364222, 489575145313, 209592936754, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5792 = true := by
  decide +kernel

theorem tot5792 : totK PD2M8K2 D2M8K2.t5792 = [176029280355, 470859950011, 231934078594, 13036214911, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5793 = true := by
  decide +kernel

theorem tot5793 : totK PD2M8K2 D2M8K2.t5793 = [0, 291643738430, 506425528693, 99446183343, 1092001298, 0, 0, 0] := by
  decide +kernel

theorem rows5794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5794 = true := by
  decide +kernel

theorem tot5794 : totK PD2M8K2 D2M8K2.t5794 = [89322763288, 327392870301, 367586608136, 100839686546, 3867150671, 0, 0, 0] := by
  decide +kernel

theorem rows5795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5795 = true := by
  decide +kernel

theorem tot5795 : totK PD2M8K2 D2M8K2.t5795 = [166013880916, 444333172319, 273396857411, 30191107111, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

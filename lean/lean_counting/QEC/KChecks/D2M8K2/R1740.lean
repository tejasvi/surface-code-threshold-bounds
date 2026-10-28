import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6960 = true := by
  decide +kernel

theorem tot6960 : totK PD2M8K2 D2M8K2.t6960 = [0, 176801703987, 448689928093, 266112675719, 20484579662, 0, 0, 0] := by
  decide +kernel

theorem rows6961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6961 = true := by
  decide +kernel

theorem tot6961 : totK PD2M8K2 D2M8K2.t6961 = [0, 89076128973, 368638349019, 365215255620, 68767524012, 1164319620, 0, 0] := by
  decide +kernel

theorem rows6962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6962 = true := by
  decide +kernel

theorem tot6962 : totK PD2M8K2 D2M8K2.t6962 = [0, 0, 252270363031, 489591789431, 154738116249, 8423393484, 0, 0] := by
  decide +kernel

theorem rows6963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6963 = true := by
  decide +kernel

theorem tot6963 : totK PD2M8K2 D2M8K2.t6963 = [0, 118433718873, 348252845662, 322461972785, 85577057883, 3462014130, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

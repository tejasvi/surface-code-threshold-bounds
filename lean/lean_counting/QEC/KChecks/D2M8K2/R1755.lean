import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7020 = true := by
  decide +kernel

theorem tot7020 : totK PD2M8K2 D2M8K2.t7020 = [0, 180222879704, 463206375169, 252965640517, 22769043942, 0, 0, 0] := by
  decide +kernel

theorem rows7021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7021 = true := by
  decide +kernel

theorem tot7021 : totK PD2M8K2 D2M8K2.t7021 = [0, 157484804317, 463962477759, 263816722812, 16013100838, 0, 0, 0] := by
  decide +kernel

theorem rows7022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7022 = true := by
  decide +kernel

theorem tot7022 : totK PD2M8K2 D2M8K2.t7022 = [0, 0, 270375493669, 513215329971, 109291466026, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7023 = true := by
  decide +kernel

theorem tot7023 : totK PD2M8K2 D2M8K2.t7023 = [0, 64599357384, 246478157332, 396696002591, 150948857232, 7393276268, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

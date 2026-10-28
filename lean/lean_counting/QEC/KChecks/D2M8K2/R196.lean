import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t784 = true := by
  decide +kernel

theorem tot784 : totK PD2M8K2 D2M8K2.t784 = [0, 0, 192695834317, 462951017694, 207539922952, 12251875289, 0, 0] := by
  decide +kernel

theorem rows785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t785 = true := by
  decide +kernel

theorem tot785 : totK PD2M8K2 D2M8K2.t785 = [0, 0, 182726007204, 491717200647, 197044432732, 10090831696, 0, 0] := by
  decide +kernel

theorem rows786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t786 = true := by
  decide +kernel

theorem tot786 : totK PD2M8K2 D2M8K2.t786 = [0, 0, 181240683168, 466901785072, 199434373138, 10862513214, 0, 0] := by
  decide +kernel

theorem rows787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t787 = true := by
  decide +kernel

theorem tot787 : totK PD2M8K2 D2M8K2.t787 = [0, 0, 208443750382, 484779556822, 183518546406, 5203004677, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

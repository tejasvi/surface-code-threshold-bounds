import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4880 = true := by
  decide +kernel

theorem tot4880 : totK PD2M8K2 D2M8K2.t4880 = [0, 0, 0, 195027454931, 471363814105, 215769752371, 12439805748, 0] := by
  decide +kernel

theorem rows4881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4881 = true := by
  decide +kernel

theorem tot4881 : totK PD2M8K2 D2M8K2.t4881 = [0, 0, 0, 11767479273, 370090533745, 456447769727, 55052477649, 0] := by
  decide +kernel

theorem rows4882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4882 = true := by
  decide +kernel

theorem tot4882 : totK PD2M8K2 D2M8K2.t4882 = [0, 0, 0, 53071801651, 245364569722, 403323036068, 146062650802, 5757108999] := by
  decide +kernel

theorem rows4883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4883 = true := by
  decide +kernel

theorem tot4883 : totK PD2M8K2 D2M8K2.t4883 = [0, 0, 0, 172529559610, 483980173656, 194481489361, 10922323554, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

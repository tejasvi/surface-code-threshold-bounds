import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9884 = true := by
  decide +kernel

theorem tot9884 : totK PD2M8K2 D2M8K2.t9884 = [0, 0, 178976943830, 467678200794, 242599972047, 13908012088, 0, 0] := by
  decide +kernel

theorem rows9885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9885 = true := by
  decide +kernel

theorem tot9885 : totK PD2M8K2 D2M8K2.t9885 = [0, 0, 205434622667, 474486356605, 203831104290, 7902352020, 0, 0] := by
  decide +kernel

theorem rows9886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9886 = true := by
  decide +kernel

theorem tot9886 : totK PD2M8K2 D2M8K2.t9886 = [0, 0, 182403360205, 452560335870, 226151712058, 18097452370, 0, 0] := by
  decide +kernel

theorem rows9887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9887 = true := by
  decide +kernel

theorem tot9887 : totK PD2M8K2 D2M8K2.t9887 = [0, 0, 110304537523, 438464886192, 300723377174, 25976059458, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

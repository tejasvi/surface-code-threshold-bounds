import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13836 = true := by
  decide +kernel

theorem tot13836 : totK PD2M8K2 D2M8K2.t13836 = [0, 213623160966, 486935141329, 187942279461, 7416187986, 0, 0, 0] := by
  decide +kernel

theorem rows13837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13837 = true := by
  decide +kernel

theorem tot13837 : totK PD2M8K2 D2M8K2.t13837 = [0, 172879891149, 468697540896, 228732253699, 14692331624, 0, 0, 0] := by
  decide +kernel

theorem rows13838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13838 = true := by
  decide +kernel

theorem tot13838 : totK PD2M8K2 D2M8K2.t13838 = [0, 151351491967, 454914850693, 262751691702, 16249658643, 0, 0, 0] := by
  decide +kernel

theorem rows13839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13839 = true := by
  decide +kernel

theorem tot13839 : totK PD2M8K2 D2M8K2.t13839 = [0, 0, 283659937725, 483914888468, 91585110682, 1206465782, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

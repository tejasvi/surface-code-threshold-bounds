import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5132 = true := by
  decide +kernel

theorem tot5132 : totK PD2M8K2 D2M8K2.t5132 = [0, 0, 159629658776, 436544761247, 263129034967, 51146151693, 2348208889, 0] := by
  decide +kernel

theorem rows5133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5133 = true := by
  decide +kernel

theorem tot5133 : totK PD2M8K2 D2M8K2.t5133 = [0, 0, 171958053847, 443116685202, 263684672223, 21146226027, 0, 0] := by
  decide +kernel

theorem rows5134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5134 = true := by
  decide +kernel

theorem tot5134 : totK PD2M8K2 D2M8K2.t5134 = [0, 0, 91681601894, 410880711764, 355019415600, 43185135337, 0, 0] := by
  decide +kernel

theorem rows5135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5135 = true := by
  decide +kernel

theorem tot5135 : totK PD2M8K2 D2M8K2.t5135 = [0, 0, 0, 288514810572, 522133978275, 101335706592, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

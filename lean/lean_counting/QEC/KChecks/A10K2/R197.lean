import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t788 = true := by
  decide +kernel

theorem tot788 : totK PA10K2 A10K2.t788 = [0, 0, 358784360830, 1649758657992, 1993021875861, 569300269417, 31772334738, 0, 0, 0] := by
  decide +kernel

theorem rows789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t789 = true := by
  decide +kernel

theorem tot789 : totK PA10K2 A10K2.t789 = [0, 307133734239, 758067925261, 929577170827, 1487853893613, 978909241799, 166421390822, 5676195732, 0, 0] := by
  decide +kernel

theorem rows790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t790 = true := by
  decide +kernel

theorem tot790 : totK PA10K2 A10K2.t790 = [0, 494216004638, 1851117501284, 2006875798940, 554182924337, 31301336365, 0, 0, 0, 0] := by
  decide +kernel

theorem rows791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t791 = true := by
  decide +kernel

theorem tot791 : totK PA10K2 A10K2.t791 = [0, 0, 698432472722, 2123029231910, 1674667237733, 386017911195, 25313348169, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

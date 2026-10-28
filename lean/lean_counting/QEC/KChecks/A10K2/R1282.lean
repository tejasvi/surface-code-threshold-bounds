import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5128 = true := by
  decide +kernel

theorem tot5128 : totK PA10K2 A10K2.t5128 = [0, 112562677656, 850373882019, 2033612248176, 1461972255186, 248638969737, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5129 = true := by
  decide +kernel

theorem tot5129 : totK PA10K2 A10K2.t5129 = [0, 349044501394, 1601240709536, 2184428847179, 787320994030, 53679850055, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5130 = true := by
  decide +kernel

theorem tot5130 : totK PA10K2 A10K2.t5130 = [0, 0, 581812606047, 1991755007943, 1903557673707, 427598992026, 12926121504, 0, 0, 0] := by
  decide +kernel

theorem rows5131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5131 = true := by
  decide +kernel

theorem tot5131 : totK PA10K2 A10K2.t5131 = [0, 0, 490383956341, 1803120598167, 1904606028010, 536908044691, 32523532663, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

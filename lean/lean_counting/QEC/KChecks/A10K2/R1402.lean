import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5608 = true := by
  decide +kernel

theorem tot5608 : totK PA10K2 A10K2.t5608 = [0, 0, 332048780867, 1530940719480, 2171137900455, 922423798793, 77503898295, 0, 0, 0] := by
  decide +kernel

theorem rows5609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5609 = true := by
  decide +kernel

theorem tot5609 : totK PA10K2 A10K2.t5609 = [0, 0, 0, 759506126277, 2276921806246, 1665567773879, 271214400690, 6853348008, 0, 0] := by
  decide +kernel

theorem rows5610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5610 = true := by
  decide +kernel

theorem tot5610 : totK PA10K2 A10K2.t5610 = [0, 0, 0, 457747857500, 1764402293198, 1917790972672, 504569313383, 31222411477, 0, 0] := by
  decide +kernel

theorem rows5611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5611 = true := by
  decide +kernel

theorem tot5611 : totK PA10K2 A10K2.t5611 = [0, 0, 0, 106735274700, 1028697500519, 1989359902685, 1324270052771, 300186671136, 25239774317, 0] := by
  decide +kernel

end QECKChecks.A10K2

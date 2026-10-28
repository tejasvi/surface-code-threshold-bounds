import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t804 = true := by
  decide +kernel

theorem tot804 : totK PA10K2 A10K2.t804 = [162737985116, 1118630099201, 2174456915621, 1414567203129, 265173313719, 6840736825, 0, 0, 0, 0] := by
  decide +kernel

theorem rows805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t805 = true := by
  decide +kernel

theorem tot805 : totK PA10K2 A10K2.t805 = [0, 495815436108, 1911117849429, 2045489964988, 538388278369, 18784622171, 0, 0, 0, 0] := by
  decide +kernel

theorem rows806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t806 = true := by
  decide +kernel

theorem tot806 : totK PA10K2 A10K2.t806 = [0, 553428601543, 1809691832502, 1789100744696, 630769782991, 63765033835, 0, 0, 0, 0] := by
  decide +kernel

theorem rows807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t807 = true := by
  decide +kernel

theorem tot807 : totK PA10K2 A10K2.t807 = [0, 292243983067, 1526891174934, 2210951066338, 836042141474, 61866981726, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

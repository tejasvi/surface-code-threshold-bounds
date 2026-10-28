import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6624 = true := by
  decide +kernel

theorem tot6624 : totK PA10K2 A10K2.t6624 = [0, 0, 537935706076, 1943581849969, 1999633413752, 564241476760, 32418145577, 0, 0, 0] := by
  decide +kernel

theorem rows6625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6625 = true := by
  decide +kernel

theorem tot6625 : totK PA10K2 A10K2.t6625 = [0, 282573750534, 1045876808141, 1615522724604, 1454143673439, 572226560866, 50555834002, 0, 0, 0] := by
  decide +kernel

theorem rows6626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6626 = true := by
  decide +kernel

theorem tot6626 : totK PA10K2 A10K2.t6626 = [0, 400298147522, 1695793610995, 2147578038369, 819130866541, 66524874038, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6627 = true := by
  decide +kernel

theorem tot6627 : totK PA10K2 A10K2.t6627 = [0, 114484931651, 804480225064, 2040291934252, 1687919170081, 364029289521, 12473006693, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

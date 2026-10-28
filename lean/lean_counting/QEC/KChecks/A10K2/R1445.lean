import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5780 = true := by
  decide +kernel

theorem tot5780 : totK PA10K2 A10K2.t5780 = [0, 0, 0, 524186088667, 1816305463971, 1882807937801, 500696268008, 31222411477, 0, 0] := by
  decide +kernel

theorem rows5781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5781 = true := by
  decide +kernel

theorem tot5781 : totK PA10K2 A10K2.t5781 = [0, 0, 0, 0, 876030534636, 2138996976097, 1389655545893, 305669288753, 25239774317, 0] := by
  decide +kernel

theorem rows5782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5782 = true := by
  decide +kernel

theorem tot5782 : totK PA10K2 A10K2.t5782 = [0, 0, 0, 286129387025, 1310222044106, 1900932877950, 1005094186496, 165479464370, 5410721913, 0] := by
  decide +kernel

theorem rows5783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5783 = true := by
  decide +kernel

theorem tot5783 : totK PA10K2 A10K2.t5783 = [0, 0, 0, 450482112308, 1773797292474, 1943439184013, 452948289909, 12254448589, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

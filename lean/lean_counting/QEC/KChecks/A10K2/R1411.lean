import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5644 = true := by
  decide +kernel

theorem tot5644 : totK PA10K2 A10K2.t5644 = [0, 0, 512888229923, 1786140339710, 1867697542427, 528414068313, 31936107789, 0, 0, 0] := by
  decide +kernel

theorem rows5645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5645 = true := by
  decide +kernel

theorem tot5645 : totK PA10K2 A10K2.t5645 = [0, 0, 161606955316, 1296508072860, 2242158648715, 905467197924, 57074442438, 0, 0, 0] := by
  decide +kernel

theorem rows5646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5646 = true := by
  decide +kernel

theorem tot5646 : totK PA10K2 A10K2.t5646 = [0, 0, 366095104304, 1373993690782, 1848851168160, 1033734997221, 182658087072, 6121173289, 0, 0] := by
  decide +kernel

theorem rows5647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5647 = true := by
  decide +kernel

theorem tot5647 : totK PA10K2 A10K2.t5647 = [0, 273815470041, 955489105764, 1508427237383, 1555589973924, 607177024044, 42528841868, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

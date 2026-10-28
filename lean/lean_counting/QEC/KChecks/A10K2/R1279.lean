import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5116 = true := by
  decide +kernel

theorem tot5116 : totK PA10K2 A10K2.t5116 = [0, 17179869184, 786684616702, 2144244321479, 1702912312386, 313621103511, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows5117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5117 = true := by
  decide +kernel

theorem tot5117 : totK PA10K2 A10K2.t5117 = [0, 0, 576458913614, 1904541075752, 1769594649662, 475190065678, 31559907735, 0, 0, 0] := by
  decide +kernel

theorem rows5118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5118 = true := by
  decide +kernel

theorem tot5118 : totK PA10K2 A10K2.t5118 = [0, 0, 219094637256, 1347967330379, 2213058248979, 857392879533, 66054176531, 0, 0, 0] := by
  decide +kernel

theorem rows5119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5119 = true := by
  decide +kernel

theorem tot5119 : totK PA10K2 A10K2.t5119 = [0, 0, 149149488468, 836468286800, 1743204749775, 1400611001682, 381934317193, 30220878370, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

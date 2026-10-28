import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5056 = true := by
  decide +kernel

theorem tot5056 : totK PA10K2 A10K2.t5056 = [0, 539891055239, 1896446105406, 1775493360816, 442976290337, 26521581199, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5057 = true := by
  decide +kernel

theorem tot5057 : totK PA10K2 A10K2.t5057 = [0, 0, 941865572158, 2366813826852, 1243922032427, 113465830358, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5058 = true := by
  decide +kernel

theorem tot5058 : totK PA10K2 A10K2.t5058 = [0, 0, 441156344574, 1810533829620, 1984372547401, 535018386436, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows5059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5059 = true := by
  decide +kernel

theorem tot5059 : totK PA10K2 A10K2.t5059 = [0, 0, 545235543234, 1960144919264, 1874876873333, 421730374783, 13149912228, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4032 = true := by
  decide +kernel

theorem tot4032 : totK PA10K2 A10K2.t4032 = [0, 0, 329604733505, 1483322064446, 2099100803765, 837687667074, 67674839409, 0, 0, 0] := by
  decide +kernel

theorem rows4033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4033 = true := by
  decide +kernel

theorem tot4033 : totK PA10K2 A10K2.t4033 = [0, 0, 395318379600, 1669898269231, 2047607179014, 782435761113, 69184822540, 0, 0, 0] := by
  decide +kernel

theorem rows4034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4034 = true := by
  decide +kernel

theorem tot4034 : totK PA10K2 A10K2.t4034 = [0, 0, 114484931651, 882804144075, 2072031513428, 1454950572574, 237827164326, 6904928264, 0, 0] := by
  decide +kernel

theorem rows4035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4035 = true := by
  decide +kernel

theorem tot4035 : totK PA10K2 A10K2.t4035 = [0, 0, 535132085874, 1902343544797, 1889501642520, 510698067773, 31627933639, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

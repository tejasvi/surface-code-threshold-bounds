import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4764 = true := by
  decide +kernel

theorem tot4764 : totK PA10K2 A10K2.t4764 = [0, 0, 526324111140, 1820889602306, 1779820813296, 478493517133, 44363554315, 0, 0, 0] := by
  decide +kernel

theorem rows4765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4765 = true := by
  decide +kernel

theorem tot4765 : totK PA10K2 A10K2.t4765 = [0, 0, 305832627950, 1563199302638, 2110526904129, 656688168559, 38148714322, 0, 0, 0] := by
  decide +kernel

theorem rows4766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4766 = true := by
  decide +kernel

theorem tot4766 : totK PA10K2 A10K2.t4766 = [0, 0, 278271022997, 1116261239970, 1836988736190, 1175813924917, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

theorem rows4767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4767 = true := by
  decide +kernel

theorem tot4767 : totK PA10K2 A10K2.t4767 = [0, 0, 474349284970, 1807305579789, 1971505950834, 525423542962, 31662601151, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

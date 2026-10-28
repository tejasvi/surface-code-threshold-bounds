import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6884 = true := by
  decide +kernel

theorem tot6884 : totK PA10K2 A10K2.t6884 = [0, 0, 286854300018, 1214528558827, 1802596641145, 1085192663753, 179731755693, 5410721913, 0, 0] := by
  decide +kernel

theorem rows6885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6885 = true := by
  decide +kernel

theorem tot6885 : totK PA10K2 A10K2.t6885 = [0, 0, 293457878574, 1473100287177, 2037334249805, 712879759679, 57698339944, 0, 0, 0] := by
  decide +kernel

theorem rows6886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6886 = true := by
  decide +kernel

theorem tot6886 : totK PA10K2 A10K2.t6886 = [0, 0, 296268317924, 1224771696072, 1879919631404, 1068479495916, 172144795134, 5546304973, 0, 0] := by
  decide +kernel

theorem rows6887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6887 = true := by
  decide +kernel

theorem tot6887 : totK PA10K2 A10K2.t6887 = [0, 0, 504368969528, 1901372346661, 2079647909816, 591514157751, 33588509593, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

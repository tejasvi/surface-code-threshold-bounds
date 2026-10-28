import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5796 = true := by
  decide +kernel

theorem tot5796 : totK PA10K2 A10K2.t5796 = [0, 0, 0, 507543770944, 1776553209422, 1832908128896, 480809211443, 31088438951, 0, 0] := by
  decide +kernel

theorem rows5797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5797 = true := by
  decide +kernel

theorem tot5797 : totK PA10K2 A10K2.t5797 = [0, 0, 0, 302031194261, 1513447388169, 2056149881504, 709878438699, 57778438788, 0, 0] := by
  decide +kernel

theorem rows5798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5798 = true := by
  decide +kernel

theorem tot5798 : totK PA10K2 A10K2.t5798 = [0, 0, 216429070673, 539149906393, 788836029006, 1616477548019, 1161061957383, 233528391130, 6354482628, 0] := by
  decide +kernel

theorem rows5799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5799 = true := by
  decide +kernel

theorem tot5799 : totK PA10K2 A10K2.t5799 = [0, 0, 545379115893, 1928519214619, 1925242727276, 508570519973, 31611289403, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1972 = true := by
  decide +kernel

theorem tot1972 : totK PA10K2 A10K2.t1972 = [0, 469130319405, 1819484414361, 2032284721110, 617817585738, 25055404430, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1973 = true := by
  decide +kernel

theorem tot1973 : totK PA10K2 A10K2.t1973 = [0, 0, 516630574622, 1875440098599, 1844897460125, 463453614131, 25140510525, 0, 0, 0] := by
  decide +kernel

theorem rows1974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1974 = true := by
  decide +kernel

theorem tot1974 : totK PA10K2 A10K2.t1974 = [0, 386074968241, 1492588884679, 1995719492018, 880700309797, 85903508906, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1975 = true := by
  decide +kernel

theorem tot1975 : totK PA10K2 A10K2.t1975 = [0, 343340309998, 1626194726115, 2139622091915, 838969224906, 72488782534, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

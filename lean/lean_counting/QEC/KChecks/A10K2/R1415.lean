import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5660 = true := by
  decide +kernel

theorem tot5660 : totK PA10K2 A10K2.t5660 = [0, 116150967364, 256625354356, 771389676645, 1944397037411, 1312675447911, 239904770714, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5661 = true := by
  decide +kernel

theorem tot5661 : totK PA10K2 A10K2.t5661 = [0, 545271319778, 1911294058670, 1938677516931, 542907779607, 32780555804, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5662 = true := by
  decide +kernel

theorem tot5662 : totK PA10K2 A10K2.t5662 = [0, 112467149459, 964992219033, 2059919573795, 1451118267260, 312131796046, 20328650499, 0, 0, 0] := by
  decide +kernel

theorem rows5663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5663 = true := by
  decide +kernel

theorem tot5663 : totK PA10K2 A10K2.t5663 = [0, 287800699719, 1154189566928, 1910910083447, 1373836250727, 272480316815, 11418542001, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

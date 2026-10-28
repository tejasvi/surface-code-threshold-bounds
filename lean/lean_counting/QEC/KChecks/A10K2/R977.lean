import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3908 = true := by
  decide +kernel

theorem tot3908 : totK PA10K2 A10K2.t3908 = [0, 0, 504850548399, 1888057855751, 2085133734796, 622039750239, 25414481580, 0, 0, 0] := by
  decide +kernel

theorem rows3909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3909 = true := by
  decide +kernel

theorem tot3909 : totK PA10K2 A10K2.t3909 = [0, 0, 0, 707455105772, 2178325434325, 1818561090041, 329053096218, 6853348008, 0, 0] := by
  decide +kernel

theorem rows3910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3910 = true := by
  decide +kernel

theorem tot3910 : totK PA10K2 A10K2.t3910 = [0, 0, 0, 483576386106, 1835292542760, 1928994735677, 607826332870, 48453447732, 0, 0] := by
  decide +kernel

theorem rows3911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3911 = true := by
  decide +kernel

theorem tot3911 : totK PA10K2 A10K2.t3911 = [0, 0, 0, 520965118081, 1872313921702, 1883055312053, 476603154297, 17742097974, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

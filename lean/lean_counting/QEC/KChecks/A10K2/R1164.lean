import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4656 = true := by
  decide +kernel

theorem tot4656 : totK PA10K2 A10K2.t4656 = [0, 0, 581689176278, 1974100610392, 1771918634679, 429901716961, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows4657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4657 = true := by
  decide +kernel

theorem tot4657 : totK PA10K2 A10K2.t4657 = [0, 365166370945, 1381828774171, 1752092161732, 1025610651629, 185750430138, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows4658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4658 = true := by
  decide +kernel

theorem tot4658 : totK PA10K2 A10K2.t4658 = [0, 360175607109, 1598619228544, 2047612653003, 662520679315, 38312905762, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4659 = true := by
  decide +kernel

theorem tot4659 : totK PA10K2 A10K2.t4659 = [0, 66528604465, 762757690015, 2066841332536, 1455774212916, 223382956298, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

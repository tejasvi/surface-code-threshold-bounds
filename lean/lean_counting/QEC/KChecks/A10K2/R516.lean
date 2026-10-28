import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2064 = true := by
  decide +kernel

theorem tot2064 : totK PA10K2 A10K2.t2064 = [613328696870, 2045185554911, 1925782268976, 477091798623, 25997994148, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2065 = true := by
  decide +kernel

theorem tot2065 : totK PA10K2 A10K2.t2065 = [0, 766743110563, 2227891317658, 1623899339580, 271296349743, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2066 = true := by
  decide +kernel

theorem tot2066 : totK PA10K2 A10K2.t2066 = [0, 406938025339, 1695667849383, 2145894292273, 751531277599, 56143165367, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2067 = true := by
  decide +kernel

theorem tot2067 : totK PA10K2 A10K2.t2067 = [0, 435552481792, 1762721793196, 2082653470414, 752422275476, 64977684885, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5596 = true := by
  decide +kernel

theorem tot5596 : totK PA10K2 A10K2.t5596 = [0, 202896141557, 1201768967187, 2165106039940, 1276531882054, 211779990640, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows5597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5597 = true := by
  decide +kernel

theorem tot5597 : totK PA10K2 A10K2.t5597 = [0, 0, 612612752922, 2042102193179, 1857644019515, 445689950797, 25527529665, 0, 0, 0] := by
  decide +kernel

theorem rows5598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5598 = true := by
  decide +kernel

theorem tot5598 : totK PA10K2 A10K2.t5598 = [0, 0, 464509768748, 1798126739977, 2020716894517, 655148675179, 42502615453, 0, 0, 0] := by
  decide +kernel

theorem rows5599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5599 = true := by
  decide +kernel

theorem tot5599 : totK PA10K2 A10K2.t5599 = [0, 0, 0, 722891530740, 2255551408777, 1588109566299, 253968242489, 6904928264, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

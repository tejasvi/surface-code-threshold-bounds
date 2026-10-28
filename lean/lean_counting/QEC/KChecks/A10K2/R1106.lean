import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4424 = true := by
  decide +kernel

theorem tot4424 : totK PA10K2 A10K2.t4424 = [0, 204931613098, 1398298309475, 2183630707886, 857152606530, 65147571409, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4425 = true := by
  decide +kernel

theorem tot4425 : totK PA10K2 A10K2.t4425 = [0, 486355993374, 1542105874510, 1780998748191, 911817785611, 155128127268, 5976421810, 0, 0, 0] := by
  decide +kernel

theorem rows4426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4426 = true := by
  decide +kernel

theorem tot4426 : totK PA10K2 A10K2.t4426 = [0, 316555443509, 1547753985909, 2228601229104, 922702961335, 78634367830, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4427 = true := by
  decide +kernel

theorem tot4427 : totK PA10K2 A10K2.t4427 = [0, 0, 605557549678, 2054484391759, 1993041023203, 446370453335, 13543209714, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

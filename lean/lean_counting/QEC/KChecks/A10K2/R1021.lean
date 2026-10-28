import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4084 = true := by
  decide +kernel

theorem tot4084 : totK PA10K2 A10K2.t4084 = [0, 655663478356, 2041328134906, 1665372052111, 397995866641, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4085 = true := by
  decide +kernel

theorem tot4085 : totK PA10K2 A10K2.t4085 = [293873915135, 1190154649607, 1875789904596, 1247256975116, 210614096898, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4086 = true := by
  decide +kernel

theorem tot4086 : totK PA10K2 A10K2.t4086 = [433290635575, 1722265789751, 1881306739032, 517056595246, 31842501065, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4087 = true := by
  decide +kernel

theorem tot4087 : totK PA10K2 A10K2.t4087 = [0, 724228342706, 2246864813839, 1479746003496, 168721496731, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

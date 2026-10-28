import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A9

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows7612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7612 = true := by
  rw [show A10K2.u7612 = KTree.node A10K2.u7610 (nat_lit 123667377) (nat_lit 9107130710) (nat_lit 0) A10K2.u7611 from rfl, allE_node, arows7610, irow7612, arows7611]
  all_goals rfl

theorem atot7612 : totK PA10K2 A10K2.u7612 = [0, 0, 843794753437, 4183066951258, 7716200448170, 5926787101047, 1483020288172, 80939540425, 0, 0] := by
  rw [show A10K2.u7612 = KTree.node A10K2.u7610 (nat_lit 123667377) (nat_lit 9107130710) (nat_lit 0) A10K2.u7611 from rfl, totK_node, atot7610, atot7611]
  decide +kernel

theorem arows7615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7615 = true := by
  rw [show A10K2.u7615 = KTree.node A10K2.u7613 (nat_lit 123680703) (nat_lit 10605133796) (nat_lit 0) A10K2.u7614 from rfl, allE_node, arows7613, irow7615, arows7614]
  all_goals rfl

theorem atot7615 : totK PA10K2 A10K2.u7615 = [0, 0, 1466422210342, 5984168004466, 7972950667883, 3871135376364, 537320398675, 12219140272, 0, 0] := by
  rw [show A10K2.u7615 = KTree.node A10K2.u7613 (nat_lit 123680703) (nat_lit 10605133796) (nat_lit 0) A10K2.u7614 from rfl, totK_node, atot7613, atot7614]
  decide +kernel

theorem arows7619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7619 = true := by
  rw [show A10K2.u7619 = KTree.node A10K2.u7617 (nat_lit 123699072) (nat_lit 14522045214) (nat_lit 0) A10K2.u7618 from rfl, allE_node, arows7617, irow7619, arows7618]
  all_goals rfl

theorem atot7619 : totK PA10K2 A10K2.u7619 = [0, 0, 17179869184, 2078175176932, 7136092813942, 7780554202720, 2767731243848, 291874554963, 6318667960, 0] := by
  rw [show A10K2.u7619 = KTree.node A10K2.u7617 (nat_lit 123699072) (nat_lit 14522045214) (nat_lit 0) A10K2.u7618 from rfl, totK_node, atot7617, atot7618]
  decide +kernel

theorem arows7622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7622 = true := by
  rw [show A10K2.u7622 = KTree.node A10K2.u7620 (nat_lit 123712755) (nat_lit 10070790899) (nat_lit 0) A10K2.u7621 from rfl, allE_node, arows7620, irow7622, arows7621]
  all_goals rfl

theorem atot7622 : totK PA10K2 A10K2.u7622 = [0, 0, 0, 1453956707916, 6161169739686, 8243950254598, 3541038731835, 367088992018, 6439430839, 0] := by
  rw [show A10K2.u7622 = KTree.node A10K2.u7620 (nat_lit 123712755) (nat_lit 10070790899) (nat_lit 0) A10K2.u7621 from rfl, totK_node, atot7620, atot7621]
  decide +kernel

theorem arows7627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7627 = true := by
  rw [show A10K2.u7627 = KTree.node A10K2.u7625 (nat_lit 123731556) (nat_lit 2847052352) (nat_lit 0) A10K2.u7626 from rfl, allE_node, arows7625, irow7627, arows7626]
  all_goals rfl

theorem atot7627 : totK PA10K2 A10K2.u7627 = [0, 0, 872244600920, 3378108987196, 5233436739749, 5394795029101, 3774927001386, 961189328672, 61018386929, 0] := by
  rw [show A10K2.u7627 = KTree.node A10K2.u7625 (nat_lit 123731556) (nat_lit 2847052352) (nat_lit 0) A10K2.u7626 from rfl, totK_node, atot7625, atot7626]
  decide +kernel

theorem arows7630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7630 = true := by
  rw [show A10K2.u7630 = KTree.node A10K2.u7628 (nat_lit 124339704) (nat_lit 9796339608) (nat_lit 0) A10K2.u7629 from rfl, allE_node, arows7628, irow7630, arows7629]
  all_goals rfl

theorem atot7630 : totK PA10K2 A10K2.u7630 = [0, 0, 861030676128, 4555135645052, 7907925339176, 4756396468945, 861928002130, 38123231481, 0, 0] := by
  rw [show A10K2.u7630 = KTree.node A10K2.u7628 (nat_lit 124339704) (nat_lit 9796339608) (nat_lit 0) A10K2.u7629 from rfl, totK_node, atot7628, atot7629]
  decide +kernel

theorem arows7634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7634 = true := by
  rw [show A10K2.u7634 = KTree.node A10K2.u7632 (nat_lit 124352147) (nat_lit 10935650241) (nat_lit 0) A10K2.u7633 from rfl, allE_node, arows7632, irow7634, arows7633]
  all_goals rfl

theorem atot7634 : totK PA10K2 A10K2.u7634 = [0, 0, 610900211470, 3717106720546, 7765949629351, 6217605616115, 1512210192149, 74019108011, 0, 0] := by
  rw [show A10K2.u7634 = KTree.node A10K2.u7632 (nat_lit 124352147) (nat_lit 10935650241) (nat_lit 0) A10K2.u7633 from rfl, totK_node, atot7632, atot7633]
  decide +kernel

theorem arows7637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7637 = true := by
  rw [show A10K2.u7637 = KTree.node A10K2.u7635 (nat_lit 124370984) (nat_lit 9281916369) (nat_lit 0) A10K2.u7636 from rfl, allE_node, arows7635, irow7637, arows7636]
  all_goals rfl

theorem atot7637 : totK PA10K2 A10K2.u7637 = [0, 0, 0, 973898325101, 5007142284182, 7935241627691, 4164063410892, 681827671945, 31082886609, 0] := by
  rw [show A10K2.u7637 = KTree.node A10K2.u7635 (nat_lit 124370984) (nat_lit 9281916369) (nat_lit 0) A10K2.u7636 from rfl, totK_node, atot7635, atot7636]
  decide +kernel

theorem arows7643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7643 = true := by
  rw [show A10K2.u7643 = KTree.node A10K2.u7641 (nat_lit 124389598) (nat_lit 6341371308) (nat_lit 128) A10K2.u7642 from rfl, allE_node, arows7641, irow7643, arows7642]
  all_goals rfl

theorem atot7643 : totK PA10K2 A10K2.u7643 = [0, 0, 1050022894405, 4734537752502, 7165798688657, 4869564244748, 1650660356853, 197785893846, 6121173289, 0] := by
  rw [show A10K2.u7643 = KTree.node A10K2.u7641 (nat_lit 124389598) (nat_lit 6341371308) (nat_lit 128) A10K2.u7642 from rfl, totK_node, atot7641, atot7642]
  decide +kernel

theorem arows7646 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7646 = true := by
  rw [show A10K2.u7646 = KTree.node A10K2.u7644 (nat_lit 124405458) (nat_lit 15364856042) (nat_lit 0) A10K2.u7645 from rfl, allE_node, arows7644, irow7646, arows7645]
  all_goals rfl

theorem atot7646 : totK PA10K2 A10K2.u7646 = [0, 0, 743454972142, 4366796959222, 8074733115720, 4941438291999, 844826381688, 38123231481, 0, 0] := by
  rw [show A10K2.u7646 = KTree.node A10K2.u7644 (nat_lit 124405458) (nat_lit 15364856042) (nat_lit 0) A10K2.u7645 from rfl, totK_node, atot7644, atot7645]
  decide +kernel

theorem arows7650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7650 = true := by
  rw [show A10K2.u7650 = KTree.node A10K2.u7648 (nat_lit 124437269) (nat_lit 6979538597) (nat_lit 0) A10K2.u7649 from rfl, allE_node, arows7648, irow7650, arows7649]
  all_goals rfl

theorem atot7650 : totK PA10K2 A10K2.u7650 = [0, 0, 0, 1535753818463, 6564266273714, 8150331246669, 2518832153456, 174920539440, 0, 0] := by
  rw [show A10K2.u7650 = KTree.node A10K2.u7648 (nat_lit 124437269) (nat_lit 6979538597) (nat_lit 0) A10K2.u7649 from rfl, totK_node, atot7648, atot7649]
  decide +kernel

theorem arows7653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7653 = true := by
  rw [show A10K2.u7653 = KTree.node A10K2.u7651 (nat_lit 124462432) (nat_lit 7380264624) (nat_lit 0) A10K2.u7652 from rfl, allE_node, arows7651, irow7653, arows7652]
  all_goals rfl

theorem atot7653 : totK PA10K2 A10K2.u7653 = [0, 0, 1324242768764, 5682329737461, 8000885020510, 4168034311336, 912119962410, 125872114712, 6354482628, 0] := by
  rw [show A10K2.u7653 = KTree.node A10K2.u7651 (nat_lit 124462432) (nat_lit 7380264624) (nat_lit 0) A10K2.u7652 from rfl, totK_node, atot7651, atot7652]
  decide +kernel

theorem arows7658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7658 = true := by
  rw [show A10K2.u7658 = KTree.node A10K2.u7656 (nat_lit 124480897) (nat_lit 9982413561) (nat_lit 0) A10K2.u7657 from rfl, allE_node, arows7656, irow7658, arows7657]
  all_goals rfl

theorem atot7658 : totK PA10K2 A10K2.u7658 = [0, 0, 846194190982, 4454313132406, 8123347849056, 5550391296016, 1079264804068, 36824485851, 0, 0] := by
  rw [show A10K2.u7658 = KTree.node A10K2.u7656 (nat_lit 124480897) (nat_lit 9982413561) (nat_lit 0) A10K2.u7657 from rfl, totK_node, atot7656, atot7657]
  decide +kernel

theorem arows7661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7661 = true := by
  rw [show A10K2.u7661 = KTree.node A10K2.u7659 (nat_lit 124495543) (nat_lit 14381767791) (nat_lit 0) A10K2.u7660 from rfl, allE_node, arows7659, irow7661, arows7660]
  all_goals rfl

theorem atot7661 : totK PA10K2 A10K2.u7661 = [0, 0, 0, 1323085597774, 6019346743722, 8423669327382, 3880442135518, 454318128173, 7047025452, 0] := by
  rw [show A10K2.u7661 = KTree.node A10K2.u7659 (nat_lit 124495543) (nat_lit 14381767791) (nat_lit 0) A10K2.u7660 from rfl, totK_node, atot7659, atot7660]
  decide +kernel

theorem arows7665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7665 = true := by
  rw [show A10K2.u7665 = KTree.node A10K2.u7663 (nat_lit 124514316) (nat_lit 6444526285) (nat_lit 0) A10K2.u7664 from rfl, allE_node, arows7663, irow7665, arows7664]
  all_goals rfl

theorem atot7665 : totK PA10K2 A10K2.u7665 = [0, 0, 0, 1165861983799, 5225098049714, 7946182187866, 4691588011463, 882924874330, 41130295026, 0] := by
  rw [show A10K2.u7665 = KTree.node A10K2.u7663 (nat_lit 124514316) (nat_lit 6444526285) (nat_lit 0) A10K2.u7664 from rfl, totK_node, atot7663, atot7664]
  decide +kernel

theorem arows7668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7668 = true := by
  rw [show A10K2.u7668 = KTree.node A10K2.u7666 (nat_lit 124598506) (nat_lit 12403245268) (nat_lit 0) A10K2.u7667 from rfl, allE_node, arows7666, irow7668, arows7667]
  all_goals rfl

theorem atot7668 : totK PA10K2 A10K2.u7668 = [0, 0, 0, 1226690599445, 5417398435241, 7733550271271, 3915311365511, 655812147511, 31768748853, 0] := by
  rw [show A10K2.u7668 = KTree.node A10K2.u7666 (nat_lit 124598506) (nat_lit 12403245268) (nat_lit 0) A10K2.u7667 from rfl, totK_node, atot7666, atot7667]
  decide +kernel

theorem arows7678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7678 = true := by
  rw [show A10K2.u7678 = KTree.node A10K2.u7676 (nat_lit 124612024) (nat_lit 13966343215) (nat_lit 0) A10K2.u7677 from rfl, allE_node, arows7676, irow7678, arows7677]
  all_goals rfl

theorem atot7678 : totK PA10K2 A10K2.u7678 = [0, 0, 0, 780536075463, 4491718828190, 8287026807122, 5113406079914, 897770784183, 41826571807, 0] := by
  rw [show A10K2.u7678 = KTree.node A10K2.u7676 (nat_lit 124612024) (nat_lit 13966343215) (nat_lit 0) A10K2.u7677 from rfl, totK_node, atot7676, atot7677]
  decide +kernel

theorem arows7681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7681 = true := by
  rw [show A10K2.u7681 = KTree.node A10K2.u7679 (nat_lit 124631297) (nat_lit 5425898126) (nat_lit 2) A10K2.u7680 from rfl, allE_node, arows7679, irow7681, arows7680]
  all_goals rfl

theorem atot7681 : totK PA10K2 A10K2.u7681 = [0, 0, 0, 0, 1682824584527, 6467779356047, 7592059709742, 2936445979461, 364013094127, 8047840951] := by
  rw [show A10K2.u7681 = KTree.node A10K2.u7679 (nat_lit 124631297) (nat_lit 5425898126) (nat_lit 2) A10K2.u7680 from rfl, totK_node, atot7679, atot7680]
  decide +kernel

theorem arows7685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7685 = true := by
  rw [show A10K2.u7685 = KTree.node A10K2.u7683 (nat_lit 124659882) (nat_lit 12841543123) (nat_lit 0) A10K2.u7684 from rfl, allE_node, arows7683, irow7685, arows7684]
  all_goals rfl

theorem atot7685 : totK PA10K2 A10K2.u7685 = [0, 0, 0, 1216656904752, 5371358455600, 7775376626266, 4141753839118, 810294970684, 49358217965, 0] := by
  rw [show A10K2.u7685 = KTree.node A10K2.u7683 (nat_lit 124659882) (nat_lit 12841543123) (nat_lit 0) A10K2.u7684 from rfl, totK_node, atot7683, atot7684]
  decide +kernel

theorem arows7688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7688 = true := by
  rw [show A10K2.u7688 = KTree.node A10K2.u7686 (nat_lit 124672354) (nat_lit 12517783050) (nat_lit 0) A10K2.u7687 from rfl, allE_node, arows7686, irow7688, arows7687]
  all_goals rfl

theorem atot7688 : totK PA10K2 A10K2.u7688 = [0, 0, 0, 1589515293162, 6450821510895, 7971603201725, 3023875637874, 307021406920, 6354482628, 0] := by
  rw [show A10K2.u7688 = KTree.node A10K2.u7686 (nat_lit 124672354) (nat_lit 12517783050) (nat_lit 0) A10K2.u7687 from rfl, totK_node, atot7686, atot7687]
  decide +kernel

theorem arows7693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7693 = true := by
  rw [show A10K2.u7693 = KTree.node A10K2.u7691 (nat_lit 124740046) (nat_lit 14728140744) (nat_lit 0) A10K2.u7692 from rfl, allE_node, arows7691, irow7693, arows7692]
  all_goals rfl

theorem atot7693 : totK PA10K2 A10K2.u7693 = [0, 0, 0, 1143399010272, 5496241399319, 8440560313109, 4389535003646, 616915078975, 13572172291, 0] := by
  rw [show A10K2.u7693 = KTree.node A10K2.u7691 (nat_lit 124740046) (nat_lit 14728140744) (nat_lit 0) A10K2.u7692 from rfl, totK_node, atot7691, atot7692]
  decide +kernel

theorem arows7696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7696 = true := by
  rw [show A10K2.u7696 = KTree.node A10K2.u7694 (nat_lit 124857523) (nat_lit 10186011321) (nat_lit 0) A10K2.u7695 from rfl, allE_node, arows7694, irow7696, arows7695]
  all_goals rfl

theorem atot7696 : totK PA10K2 A10K2.u7696 = [0, 0, 948444040241, 4162086211407, 6600799126668, 4918132090609, 2262499038823, 566126031292, 41590655314, 0] := by
  rw [show A10K2.u7696 = KTree.node A10K2.u7694 (nat_lit 124857523) (nat_lit 10186011321) (nat_lit 0) A10K2.u7695 from rfl, totK_node, atot7694, atot7695]
  decide +kernel

theorem arows7700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7700 = true := by
  rw [show A10K2.u7700 = KTree.node A10K2.u7698 (nat_lit 124868834) (nat_lit 13231179754) (nat_lit 0) A10K2.u7699 from rfl, allE_node, arows7698, irow7700, arows7699]
  all_goals rfl

theorem atot7700 : totK PA10K2 A10K2.u7700 = [0, 0, 1239536172151, 5717575265865, 8231835764886, 3850051161913, 503095259598, 13317224979, 0, 0] := by
  rw [show A10K2.u7700 = KTree.node A10K2.u7698 (nat_lit 124868834) (nat_lit 13231179754) (nat_lit 0) A10K2.u7699 from rfl, totK_node, atot7698, atot7699]
  decide +kernel

theorem arows7703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7703 = true := by
  rw [show A10K2.u7703 = KTree.node A10K2.u7701 (nat_lit 124916256) (nat_lit 14162460222) (nat_lit 0) A10K2.u7702 from rfl, allE_node, arows7701, irow7703, arows7702]
  all_goals rfl

theorem atot7703 : totK PA10K2 A10K2.u7703 = [0, 0, 1328304200974, 5461644332111, 7764754026567, 4162962934638, 644059016732, 16724290224, 0, 0] := by
  rw [show A10K2.u7703 = KTree.node A10K2.u7701 (nat_lit 124916256) (nat_lit 14162460222) (nat_lit 0) A10K2.u7702 from rfl, totK_node, atot7701, atot7702]
  decide +kernel

theorem arows7709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7709 = true := by
  rw [show A10K2.u7709 = KTree.node A10K2.u7707 (nat_lit 124928868) (nat_lit 13549853347) (nat_lit 0) A10K2.u7708 from rfl, allE_node, arows7707, irow7709, arows7708]
  all_goals rfl

theorem atot7709 : totK PA10K2 A10K2.u7709 = [0, 0, 820824437048, 4713818882408, 8178422276694, 4608404753728, 678025067715, 31768748853, 0, 0] := by
  rw [show A10K2.u7709 = KTree.node A10K2.u7707 (nat_lit 124928868) (nat_lit 13549853347) (nat_lit 0) A10K2.u7708 from rfl, totK_node, atot7707, atot7708]
  decide +kernel

theorem arows7712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7712 = true := by
  rw [show A10K2.u7712 = KTree.node A10K2.u7710 (nat_lit 124954660) (nat_lit 13718824819) (nat_lit 0) A10K2.u7711 from rfl, allE_node, arows7710, irow7712, arows7711]
  all_goals rfl

theorem atot7712 : totK PA10K2 A10K2.u7712 = [0, 0, 0, 2157879947351, 7541671509840, 7364271812888, 1715766652633, 92104896271, 0, 0] := by
  rw [show A10K2.u7712 = KTree.node A10K2.u7710 (nat_lit 124954660) (nat_lit 13718824819) (nat_lit 0) A10K2.u7711 from rfl, totK_node, atot7710, atot7711]
  decide +kernel

theorem arows7716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7716 = true := by
  rw [show A10K2.u7716 = KTree.node A10K2.u7714 (nat_lit 125306951) (nat_lit 10510688795) (nat_lit 0) A10K2.u7715 from rfl, allE_node, arows7714, irow7716, arows7715]
  all_goals rfl

theorem atot7716 : totK PA10K2 A10K2.u7716 = [0, 0, 888016174070, 3934850045195, 6795615760598, 5593137128834, 1993478751492, 243289276660, 6354482628, 0] := by
  rw [show A10K2.u7716 = KTree.node A10K2.u7714 (nat_lit 125306951) (nat_lit 10510688795) (nat_lit 0) A10K2.u7715 from rfl, totK_node, atot7714, atot7715]
  decide +kernel

theorem arows7719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7719 = true := by
  rw [show A10K2.u7719 = KTree.node A10K2.u7717 (nat_lit 125334422) (nat_lit 15546589064) (nat_lit 0) A10K2.u7718 from rfl, allE_node, arows7717, irow7719, arows7718]
  all_goals rfl

theorem atot7719 : totK PA10K2 A10K2.u7719 = [0, 0, 714684283898, 4155043631354, 8072686360620, 6025737672216, 1420677945131, 76099179376, 0, 0] := by
  rw [show A10K2.u7719 = KTree.node A10K2.u7717 (nat_lit 125334422) (nat_lit 15546589064) (nat_lit 0) A10K2.u7718 from rfl, totK_node, atot7717, atot7718]
  decide +kernel

theorem arows7724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7724 = true := by
  rw [show A10K2.u7724 = KTree.node A10K2.u7722 (nat_lit 125363384) (nat_lit 10241397227) (nat_lit 0) A10K2.u7723 from rfl, allE_node, arows7722, irow7724, arows7723]
  all_goals rfl

theorem atot7724 : totK PA10K2 A10K2.u7724 = [0, 0, 542450728586, 2880553148616, 6485290347793, 7018946661221, 2780731285601, 305664075763, 7237400819, 0] := by
  rw [show A10K2.u7724 = KTree.node A10K2.u7722 (nat_lit 125363384) (nat_lit 10241397227) (nat_lit 0) A10K2.u7723 from rfl, totK_node, atot7722, atot7723]
  decide +kernel

theorem arows7727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7727 = true := by
  rw [show A10K2.u7727 = KTree.node A10K2.u7725 (nat_lit 125386119) (nat_lit 14491572015) (nat_lit 0) A10K2.u7726 from rfl, allE_node, arows7725, irow7727, arows7726]
  all_goals rfl

theorem atot7727 : totK PA10K2 A10K2.u7727 = [0, 0, 981193120400, 4737241341925, 7965699148987, 4759680271934, 851457612459, 37750801259, 0, 0] := by
  rw [show A10K2.u7727 = KTree.node A10K2.u7725 (nat_lit 125386119) (nat_lit 14491572015) (nat_lit 0) A10K2.u7726 from rfl, totK_node, atot7725, atot7726]
  decide +kernel

theorem arows7731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7731 = true := by
  rw [show A10K2.u7731 = KTree.node A10K2.u7729 (nat_lit 125400291) (nat_lit 10410920891) (nat_lit 0) A10K2.u7730 from rfl, allE_node, arows7729, irow7731, arows7730]
  all_goals rfl

theorem atot7731 : totK PA10K2 A10K2.u7731 = [0, 0, 659363822726, 4046179716356, 8002389528710, 5919852052115, 1467068952222, 89191227119, 0, 0] := by
  rw [show A10K2.u7731 = KTree.node A10K2.u7729 (nat_lit 125400291) (nat_lit 10410920891) (nat_lit 0) A10K2.u7730 from rfl, totK_node, atot7729, atot7730]
  decide +kernel

theorem arows7734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7734 = true := by
  rw [show A10K2.u7734 = KTree.node A10K2.u7732 (nat_lit 125418965) (nat_lit 3006356021) (nat_lit 0) A10K2.u7733 from rfl, allE_node, arows7732, irow7734, arows7733]
  all_goals rfl

theorem atot7734 : totK PA10K2 A10K2.u7734 = [0, 0, 0, 1084134662290, 5364494669830, 8329391445490, 4060507596414, 543125836144, 13576218110, 0] := by
  rw [show A10K2.u7734 = KTree.node A10K2.u7732 (nat_lit 125418965) (nat_lit 3006356021) (nat_lit 0) A10K2.u7733 from rfl, totK_node, atot7732, atot7733]
  decide +kernel

theorem arows7741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7741 = true := by
  rw [show A10K2.u7741 = KTree.node A10K2.u7739 (nat_lit 125504575) (nat_lit 14140654769) (nat_lit 0) A10K2.u7740 from rfl, allE_node, arows7739, irow7741, arows7740]
  all_goals rfl

theorem atot7741 : totK PA10K2 A10K2.u7741 = [0, 0, 985345008910, 4656273394909, 7787607949338, 5310092446062, 1344892219830, 81743127112, 0, 0] := by
  rw [show A10K2.u7741 = KTree.node A10K2.u7739 (nat_lit 125504575) (nat_lit 14140654769) (nat_lit 0) A10K2.u7740 from rfl, totK_node, atot7739, atot7740]
  decide +kernel

theorem arows7744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7744 = true := by
  rw [show A10K2.u7744 = KTree.node A10K2.u7742 (nat_lit 125516446) (nat_lit 11905083190) (nat_lit 0) A10K2.u7743 from rfl, allE_node, arows7742, irow7744, arows7743]
  all_goals rfl

theorem atot7744 : totK PA10K2 A10K2.u7744 = [0, 0, 1361858516948, 5740176226986, 8042072695915, 4072340080593, 630021016182, 18682938825, 0, 0] := by
  rw [show A10K2.u7744 = KTree.node A10K2.u7742 (nat_lit 125516446) (nat_lit 11905083190) (nat_lit 0) A10K2.u7743 from rfl, totK_node, atot7742, atot7743]
  decide +kernel

theorem arows7748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7748 = true := by
  rw [show A10K2.u7748 = KTree.node A10K2.u7746 (nat_lit 125534252) (nat_lit 10648118173) (nat_lit 0) A10K2.u7747 from rfl, allE_node, arows7746, irow7748, arows7747]
  all_goals rfl

theorem atot7748 : totK PA10K2 A10K2.u7748 = [0, 0, 0, 1788320484948, 6896265383605, 8112745231041, 2989880630067, 306964227118, 6632180018, 0] := by
  rw [show A10K2.u7748 = KTree.node A10K2.u7746 (nat_lit 125534252) (nat_lit 10648118173) (nat_lit 0) A10K2.u7747 from rfl, totK_node, atot7746, atot7747]
  decide +kernel

theorem arows7751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7751 = true := by
  rw [show A10K2.u7751 = KTree.node A10K2.u7749 (nat_lit 125547926) (nat_lit 15599954179) (nat_lit 0) A10K2.u7750 from rfl, allE_node, arows7749, irow7751, arows7750]
  all_goals rfl

theorem atot7751 : totK PA10K2 A10K2.u7751 = [0, 0, 0, 1522914885961, 6161984929927, 8081033613852, 3616175033883, 396754472364, 7047025452, 0] := by
  rw [show A10K2.u7751 = KTree.node A10K2.u7749 (nat_lit 125547926) (nat_lit 15599954179) (nat_lit 0) A10K2.u7750 from rfl, totK_node, atot7749, atot7750]
  decide +kernel

theorem arows7756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7756 = true := by
  rw [show A10K2.u7756 = KTree.node A10K2.u7754 (nat_lit 125566620) (nat_lit 7222693545) (nat_lit 0) A10K2.u7755 from rfl, allE_node, arows7754, irow7756, arows7755]
  all_goals rfl

theorem atot7756 : totK PA10K2 A10K2.u7756 = [0, 846984141050, 3149982397311, 3568640472098, 2803112617905, 4455936164189, 3787073587693, 967713448238, 61110126106, 0] := by
  rw [show A10K2.u7756 = KTree.node A10K2.u7754 (nat_lit 125566620) (nat_lit 7222693545) (nat_lit 0) A10K2.u7755 from rfl, totK_node, atot7754, atot7755]
  decide +kernel

theorem arows7759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7759 = true := by
  rw [show A10K2.u7759 = KTree.node A10K2.u7757 (nat_lit 130041128) (nat_lit 10765362436) (nat_lit 0) A10K2.u7758 from rfl, allE_node, arows7757, irow7759, arows7758]
  all_goals rfl

theorem atot7759 : totK PA10K2 A10K2.u7759 = [0, 919197997592, 4624632177584, 7847838748351, 4624506633495, 816068102442, 37186156514, 0, 0, 0] := by
  rw [show A10K2.u7759 = KTree.node A10K2.u7757 (nat_lit 130041128) (nat_lit 10765362436) (nat_lit 0) A10K2.u7758 from rfl, totK_node, atot7757, atot7758]
  decide +kernel

theorem arows7763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7763 = true := by
  rw [show A10K2.u7763 = KTree.node A10K2.u7761 (nat_lit 130055265) (nat_lit 9681585294) (nat_lit 0) A10K2.u7762 from rfl, allE_node, arows7761, irow7763, arows7762]
  all_goals rfl

theorem atot7763 : totK PA10K2 A10K2.u7763 = [0, 465644095695, 3439209666144, 7832187796837, 6481893434701, 1604462812037, 94137422447, 0, 0, 0] := by
  rw [show A10K2.u7763 = KTree.node A10K2.u7761 (nat_lit 130055265) (nat_lit 9681585294) (nat_lit 0) A10K2.u7762 from rfl, totK_node, atot7761, atot7762]
  decide +kernel

theorem arows7766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7766 = true := by
  rw [show A10K2.u7766 = KTree.node A10K2.u7764 (nat_lit 130073144) (nat_lit 14453644427) (nat_lit 0) A10K2.u7765 from rfl, allE_node, arows7764, irow7766, arows7765]
  all_goals rfl

theorem atot7766 : totK PA10K2 A10K2.u7766 = [0, 0, 876580496516, 4758932694815, 7961988160178, 4376720302667, 782632951615, 36196801203, 0, 0] := by
  rw [show A10K2.u7766 = KTree.node A10K2.u7764 (nat_lit 130073144) (nat_lit 14453644427) (nat_lit 0) A10K2.u7765 from rfl, totK_node, atot7764, atot7765]
  decide +kernel

theorem arows7772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7772 = true := by
  rw [show A10K2.u7772 = KTree.node A10K2.u7770 (nat_lit 130157062) (nat_lit 12722321469) (nat_lit 0) A10K2.u7771 from rfl, allE_node, arows7770, irow7772, arows7771]
  all_goals rfl

theorem atot7772 : totK PA10K2 A10K2.u7772 = [0, 869012584198, 4216660807384, 7567873018136, 5600815853080, 1433953037561, 88315261492, 0, 0, 0] := by
  rw [show A10K2.u7772 = KTree.node A10K2.u7770 (nat_lit 130157062) (nat_lit 12722321469) (nat_lit 0) A10K2.u7771 from rfl, totK_node, atot7770, atot7771]
  decide +kernel

theorem arows7775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7775 = true := by
  rw [show A10K2.u7775 = KTree.node A10K2.u7773 (nat_lit 130187556) (nat_lit 13732563620) (nat_lit 0) A10K2.u7774 from rfl, allE_node, arows7773, irow7775, arows7774]
  all_goals rfl

theorem atot7775 : totK PA10K2 A10K2.u7775 = [0, 449936922972, 3612633438945, 7913960361983, 5956752021240, 1275194886497, 69871497746, 0, 0, 0] := by
  rw [show A10K2.u7775 = KTree.node A10K2.u7773 (nat_lit 130187556) (nat_lit 13732563620) (nat_lit 0) A10K2.u7774 from rfl, totK_node, atot7773, atot7774]
  decide +kernel

theorem arows7779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7779 = true := by
  rw [show A10K2.u7779 = KTree.node A10K2.u7777 (nat_lit 130224121) (nat_lit 6072365150) (nat_lit 0) A10K2.u7778 from rfl, allE_node, arows7777, irow7779, arows7778]
  all_goals rfl

theorem atot7779 : totK PA10K2 A10K2.u7779 = [0, 1264575968411, 5269020923820, 7744382123103, 4478104035961, 823575823288, 37167109185, 0, 0, 0] := by
  rw [show A10K2.u7779 = KTree.node A10K2.u7777 (nat_lit 130224121) (nat_lit 6072365150) (nat_lit 0) A10K2.u7778 from rfl, totK_node, atot7777, atot7778]
  decide +kernel

theorem arows7782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7782 = true := by
  rw [show A10K2.u7782 = KTree.node A10K2.u7780 (nat_lit 130245811) (nat_lit 10310495083) (nat_lit 0) A10K2.u7781 from rfl, allE_node, arows7780, irow7782, arows7781]
  all_goals rfl

theorem atot7782 : totK PA10K2 A10K2.u7782 = [0, 987888954292, 5014926242041, 8388328779080, 4934029997503, 820864973063, 25449301941, 0, 0, 0] := by
  rw [show A10K2.u7782 = KTree.node A10K2.u7780 (nat_lit 130245811) (nat_lit 10310495083) (nat_lit 0) A10K2.u7781 from rfl, totK_node, atot7780, atot7781]
  decide +kernel

theorem arows7787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7787 = true := by
  rw [show A10K2.u7787 = KTree.node A10K2.u7785 (nat_lit 130256087) (nat_lit 12674228893) (nat_lit 0) A10K2.u7786 from rfl, allE_node, arows7785, irow7787, arows7786]
  all_goals rfl

theorem atot7787 : totK PA10K2 A10K2.u7787 = [0, 0, 1402884912892, 5983463265303, 8184359462069, 3698800196884, 442152350054, 6904928264, 0, 0] := by
  rw [show A10K2.u7787 = KTree.node A10K2.u7785 (nat_lit 130256087) (nat_lit 12674228893) (nat_lit 0) A10K2.u7786 from rfl, totK_node, atot7785, atot7786]
  decide +kernel

theorem arows7790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7790 = true := by
  rw [show A10K2.u7790 = KTree.node A10K2.u7788 (nat_lit 130277958) (nat_lit 13415364663) (nat_lit 0) A10K2.u7789 from rfl, allE_node, arows7788, irow7790, arows7789]
  all_goals rfl

theorem atot7790 : totK PA10K2 A10K2.u7790 = [0, 0, 1174087269989, 5422944863927, 8320001249866, 4499565081038, 589640932371, 13113983930, 0, 0] := by
  rw [show A10K2.u7790 = KTree.node A10K2.u7788 (nat_lit 130277958) (nat_lit 13415364663) (nat_lit 0) A10K2.u7789 from rfl, totK_node, atot7788, atot7789]
  decide +kernel

theorem arows7794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7794 = true := by
  rw [show A10K2.u7794 = KTree.node A10K2.u7792 (nat_lit 130288168) (nat_lit 12578888093) (nat_lit 0) A10K2.u7793 from rfl, allE_node, arows7792, irow7794, arows7793]
  all_goals rfl

theorem atot7794 : totK PA10K2 A10K2.u7794 = [0, 0, 846984141050, 4273178419399, 7515226893329, 5254348880598, 1294253934197, 85874841514, 0, 0] := by
  rw [show A10K2.u7794 = KTree.node A10K2.u7792 (nat_lit 130288168) (nat_lit 12578888093) (nat_lit 0) A10K2.u7793 from rfl, totK_node, atot7792, atot7793]
  decide +kernel

theorem arows7797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7797 = true := by
  rw [show A10K2.u7797 = KTree.node A10K2.u7795 (nat_lit 130308641) (nat_lit 9752342652) (nat_lit 0) A10K2.u7796 from rfl, allE_node, arows7795, irow7797, arows7796]
  all_goals rfl

theorem atot7797 : totK PA10K2 A10K2.u7797 = [0, 0, 1384842093287, 6000468331131, 8173144816844, 3452549994892, 370408359010, 5705019915, 0, 0] := by
  rw [show A10K2.u7797 = KTree.node A10K2.u7795 (nat_lit 130308641) (nat_lit 9752342652) (nat_lit 0) A10K2.u7796 from rfl, totK_node, atot7795, atot7796]
  decide +kernel

theorem arows7805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7805 = true := by
  rw [show A10K2.u7805 = KTree.node A10K2.u7803 (nat_lit 130320708) (nat_lit 13054302257) (nat_lit 0) A10K2.u7804 from rfl, allE_node, arows7803, irow7805, arows7804]
  all_goals rfl

theorem atot7805 : totK PA10K2 A10K2.u7805 = [0, 0, 0, 1410015531634, 6007263533605, 7929937487218, 3405139778948, 472051517423, 13364899180, 0] := by
  rw [show A10K2.u7805 = KTree.node A10K2.u7803 (nat_lit 130320708) (nat_lit 13054302257) (nat_lit 0) A10K2.u7804 from rfl, totK_node, atot7803, atot7804]
  decide +kernel

theorem arows7808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7808 = true := by
  rw [show A10K2.u7808 = KTree.node A10K2.u7806 (nat_lit 130343359) (nat_lit 14252228148) (nat_lit 0) A10K2.u7807 from rfl, allE_node, arows7806, irow7808, arows7807]
  all_goals rfl

theorem atot7808 : totK PA10K2 A10K2.u7808 = [0, 0, 539669932579, 3254031153645, 7071031997509, 6404448095680, 1901332066979, 150966418761, 0, 0] := by
  rw [show A10K2.u7808 = KTree.node A10K2.u7806 (nat_lit 130343359) (nat_lit 14252228148) (nat_lit 0) A10K2.u7807 from rfl, totK_node, atot7806, atot7807]
  decide +kernel

theorem arows7812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7812 = true := by
  rw [show A10K2.u7812 = KTree.node A10K2.u7810 (nat_lit 130433313) (nat_lit 9870704603) (nat_lit 0) A10K2.u7811 from rfl, allE_node, arows7810, irow7812, arows7811]
  all_goals rfl

theorem atot7812 : totK PA10K2 A10K2.u7812 = [0, 0, 778404762286, 4515717951982, 8248800614797, 4788213792168, 820442696674, 37186156514, 0, 0] := by
  rw [show A10K2.u7812 = KTree.node A10K2.u7810 (nat_lit 130433313) (nat_lit 9870704603) (nat_lit 0) A10K2.u7811 from rfl, totK_node, atot7810, atot7811]
  decide +kernel

theorem arows7815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7815 = true := by
  rw [show A10K2.u7815 = KTree.node A10K2.u7813 (nat_lit 130468193) (nat_lit 8951841821) (nat_lit 0) A10K2.u7814 from rfl, allE_node, arows7813, irow7815, arows7814]
  all_goals rfl

theorem atot7815 : totK PA10K2 A10K2.u7815 = [0, 0, 793104720795, 4069766234461, 7581109903937, 5662941880493, 1228732440229, 55640409804, 0, 0] := by
  rw [show A10K2.u7815 = KTree.node A10K2.u7813 (nat_lit 130468193) (nat_lit 8951841821) (nat_lit 0) A10K2.u7814 from rfl, totK_node, atot7813, atot7814]
  decide +kernel

theorem arows7820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7820 = true := by
  rw [show A10K2.u7820 = KTree.node A10K2.u7818 (nat_lit 130494135) (nat_lit 14795762680) (nat_lit 0) A10K2.u7819 from rfl, allE_node, arows7818, irow7820, arows7819]
  all_goals rfl

theorem atot7820 : totK PA10K2 A10K2.u7820 = [0, 0, 1131345380294, 5265729369319, 8246484411612, 4587927787096, 741791030743, 25608574287, 0, 0] := by
  rw [show A10K2.u7820 = KTree.node A10K2.u7818 (nat_lit 130494135) (nat_lit 14795762680) (nat_lit 0) A10K2.u7819 from rfl, totK_node, atot7818, atot7819]
  decide +kernel

theorem arows7823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7823 = true := by
  rw [show A10K2.u7823 = KTree.node A10K2.u7821 (nat_lit 130514309) (nat_lit 3429273589) (nat_lit 0) A10K2.u7822 from rfl, allE_node, arows7821, irow7823, arows7822]
  all_goals rfl

theorem atot7823 : totK PA10K2 A10K2.u7823 = [0, 849876618421, 3257098282162, 5039582723595, 5593606904029, 4017283764782, 1021458798232, 62368562949, 0, 0] := by
  rw [show A10K2.u7823 = KTree.node A10K2.u7821 (nat_lit 130514309) (nat_lit 3429273589) (nat_lit 0) A10K2.u7822 from rfl, totK_node, atot7821, atot7822]
  decide +kernel

theorem arows7827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7827 = true := by
  rw [show A10K2.u7827 = KTree.node A10K2.u7825 (nat_lit 130631018) (nat_lit 9940403154) (nat_lit 0) A10K2.u7826 from rfl, allE_node, arows7825, irow7827, arows7826]
  all_goals rfl

theorem atot7827 : totK PA10K2 A10K2.u7827 = [0, 775121153183, 4450510059591, 8079735733584, 4956181561521, 872871335994, 38123231481, 0, 0, 0] := by
  rw [show A10K2.u7827 = KTree.node A10K2.u7825 (nat_lit 130631018) (nat_lit 9940403154) (nat_lit 0) A10K2.u7826 from rfl, totK_node, atot7825, atot7826]
  decide +kernel

theorem arows7830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7830 = true := by
  rw [show A10K2.u7830 = KTree.node A10K2.u7828 (nat_lit 130643621) (nat_lit 6126192431) (nat_lit 0) A10K2.u7829 from rfl, allE_node, arows7828, irow7830, arows7829]
  all_goals rfl

theorem atot7830 : totK PA10K2 A10K2.u7830 = [0, 613166546329, 3677905147140, 7670713571380, 6213960276390, 1599646484662, 95434829234, 0, 0, 0] := by
  rw [show A10K2.u7830 = KTree.node A10K2.u7828 (nat_lit 130643621) (nat_lit 6126192431) (nat_lit 0) A10K2.u7829 from rfl, totK_node, atot7828, atot7829]
  decide +kernel

theorem arows7836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7836 = true := by
  rw [show A10K2.u7836 = KTree.node A10K2.u7834 (nat_lit 130663187) (nat_lit 9581896389) (nat_lit 0) A10K2.u7835 from rfl, allE_node, arows7834, irow7836, arows7835]
  all_goals rfl

theorem atot7836 : totK PA10K2 A10K2.u7836 = [0, 0, 909441634331, 4749943542358, 7938722889491, 4517101532661, 800524427501, 37204059898, 0, 0] := by
  rw [show A10K2.u7836 = KTree.node A10K2.u7834 (nat_lit 130663187) (nat_lit 9581896389) (nat_lit 0) A10K2.u7835 from rfl, totK_node, atot7834, atot7835]
  decide +kernel

theorem arows7839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7839 = true := by
  rw [show A10K2.u7839 = KTree.node A10K2.u7837 (nat_lit 130688769) (nat_lit 3486264068) (nat_lit 0) A10K2.u7838 from rfl, allE_node, arows7837, irow7839, arows7838]
  all_goals rfl

theorem atot7839 : totK PA10K2 A10K2.u7839 = [0, 762716802215, 4023736132882, 7611172516063, 5799474969011, 1596407245760, 108977236604, 0, 0, 0] := by
  rw [show A10K2.u7839 = KTree.node A10K2.u7837 (nat_lit 130688769) (nat_lit 3486264068) (nat_lit 0) A10K2.u7838 from rfl, totK_node, atot7837, atot7838]
  decide +kernel

theorem arows7843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7843 = true := by
  rw [show A10K2.u7843 = KTree.node A10K2.u7841 (nat_lit 130701594) (nat_lit 13440627783) (nat_lit 0) A10K2.u7842 from rfl, allE_node, arows7841, irow7843, arows7842]
  all_goals rfl

theorem atot7843 : totK PA10K2 A10K2.u7843 = [0, 561217355197, 3830104400502, 7982916259415, 5882009160128, 1201951434198, 51732975297, 0, 0, 0] := by
  rw [show A10K2.u7843 = KTree.node A10K2.u7841 (nat_lit 130701594) (nat_lit 13440627783) (nat_lit 0) A10K2.u7842 from rfl, totK_node, atot7841, atot7842]
  decide +kernel

theorem arows7846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7846 = true := by
  rw [show A10K2.u7846 = KTree.node A10K2.u7844 (nat_lit 130748356) (nat_lit 6023831822) (nat_lit 0) A10K2.u7845 from rfl, allE_node, arows7844, irow7846, arows7845]
  all_goals rfl

theorem atot7846 : totK PA10K2 A10K2.u7846 = [0, 1198932418368, 5098290609581, 7754834853992, 4726293318190, 946191902681, 50231829059, 0, 0, 0] := by
  rw [show A10K2.u7846 = KTree.node A10K2.u7844 (nat_lit 130748356) (nat_lit 6023831822) (nat_lit 0) A10K2.u7845 from rfl, totK_node, atot7844, atot7845]
  decide +kernel

theorem arows7851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7851 = true := by
  rw [show A10K2.u7851 = KTree.node A10K2.u7849 (nat_lit 130769166) (nat_lit 11211425880) (nat_lit 0) A10K2.u7850 from rfl, allE_node, arows7849, irow7851, arows7850]
  all_goals rfl

theorem atot7851 : totK PA10K2 A10K2.u7851 = [0, 1054693577800, 5111542571713, 8202721836781, 4735345999895, 794851976046, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u7851 = KTree.node A10K2.u7849 (nat_lit 130769166) (nat_lit 11211425880) (nat_lit 0) A10K2.u7850 from rfl, totK_node, atot7849, atot7850]
  decide +kernel

theorem arows7854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7854 = true := by
  rw [show A10K2.u7854 = KTree.node A10K2.u7852 (nat_lit 130780278) (nat_lit 16190745451) (nat_lit 0) A10K2.u7853 from rfl, allE_node, arows7852, irow7854, arows7853]
  all_goals rfl

theorem atot7854 : totK PA10K2 A10K2.u7854 = [0, 0, 1509897599697, 6264396698243, 8258176114134, 3621074300370, 413930954043, 6904928264, 0, 0] := by
  rw [show A10K2.u7854 = KTree.node A10K2.u7852 (nat_lit 130780278) (nat_lit 16190745451) (nat_lit 0) A10K2.u7853 from rfl, totK_node, atot7852, atot7853]
  decide +kernel

theorem arows7858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7858 = true := by
  rw [show A10K2.u7858 = KTree.node A10K2.u7856 (nat_lit 130792917) (nat_lit 3775551230) (nat_lit 0) A10K2.u7857 from rfl, allE_node, arows7856, irow7858, arows7857]
  all_goals rfl

theorem atot7858 : totK PA10K2 A10K2.u7858 = [0, 0, 1355528724895, 5954986893520, 8246658272712, 3799981238467, 426436780986, 7047025452, 0, 0] := by
  rw [show A10K2.u7858 = KTree.node A10K2.u7856 (nat_lit 130792917) (nat_lit 3775551230) (nat_lit 0) A10K2.u7857 from rfl, totK_node, atot7856, atot7857]
  decide +kernel

theorem arows7861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7861 = true := by
  rw [show A10K2.u7861 = KTree.node A10K2.u7859 (nat_lit 130885420) (nat_lit 13098636310) (nat_lit 0) A10K2.u7860 from rfl, allE_node, arows7859, irow7861, arows7860]
  all_goals rfl

theorem atot7861 : totK PA10K2 A10K2.u7861 = [0, 0, 849389605546, 4236662472235, 7565462540400, 5519495917115, 1355697153777, 86844659398, 0, 0] := by
  rw [show A10K2.u7861 = KTree.node A10K2.u7859 (nat_lit 130885420) (nat_lit 13098636310) (nat_lit 0) A10K2.u7860 from rfl, totK_node, atot7859, atot7860]
  decide +kernel

theorem arows7868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7868 = true := by
  rw [show A10K2.u7868 = KTree.node A10K2.u7866 (nat_lit 130897179) (nat_lit 10017670862) (nat_lit 0) A10K2.u7867 from rfl, allE_node, arows7866, irow7868, arows7867]
  all_goals rfl

theorem atot7868 : totK PA10K2 A10K2.u7868 = [0, 0, 1386819479308, 5865048950018, 7984277569025, 3641307507077, 461414134661, 12273889295, 0, 0] := by
  rw [show A10K2.u7868 = KTree.node A10K2.u7866 (nat_lit 130897179) (nat_lit 10017670862) (nat_lit 0) A10K2.u7867 from rfl, totK_node, atot7866, atot7867]
  decide +kernel

theorem arows7871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7871 = true := by
  rw [show A10K2.u7871 = KTree.node A10K2.u7869 (nat_lit 130917831) (nat_lit 13501697745) (nat_lit 0) A10K2.u7870 from rfl, allE_node, arows7869, irow7871, arows7870]
  all_goals rfl

theorem atot7871 : totK PA10K2 A10K2.u7871 = [0, 0, 0, 1821719239582, 6835193260902, 7660368105731, 2846198453749, 397203226825, 13576218110, 0] := by
  rw [show A10K2.u7871 = KTree.node A10K2.u7869 (nat_lit 130917831) (nat_lit 13501697745) (nat_lit 0) A10K2.u7870 from rfl, totK_node, atot7869, atot7870]
  decide +kernel

theorem arows7875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7875 = true := by
  rw [show A10K2.u7875 = KTree.node A10K2.u7873 (nat_lit 130930074) (nat_lit 14965664106) (nat_lit 0) A10K2.u7874 from rfl, allE_node, arows7873, irow7875, arows7874]
  all_goals rfl

theorem atot7875 : totK PA10K2 A10K2.u7875 = [0, 0, 304922396905, 2254034161586, 6360843975192, 7475338414232, 2832666217170, 250469238433, 0, 0] := by
  rw [show A10K2.u7875 = KTree.node A10K2.u7873 (nat_lit 130930074) (nat_lit 14965664106) (nat_lit 0) A10K2.u7874 from rfl, totK_node, atot7873, atot7874]
  decide +kernel

theorem arows7878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7878 = true := by
  rw [show A10K2.u7878 = KTree.node A10K2.u7876 (nat_lit 130955591) (nat_lit 11933677) (nat_lit 0) A10K2.u7877 from rfl, allE_node, arows7876, irow7878, arows7877]
  all_goals rfl

theorem atot7878 : totK PA10K2 A10K2.u7878 = [0, 0, 1018544825537, 5152326927264, 8241297348117, 4329137338970, 707026755857, 31768748853, 0, 0] := by
  rw [show A10K2.u7878 = KTree.node A10K2.u7876 (nat_lit 130955591) (nat_lit 11933677) (nat_lit 0) A10K2.u7877 from rfl, totK_node, atot7876, atot7877]
  decide +kernel

theorem arows7883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7883 = true := by
  rw [show A10K2.u7883 = KTree.node A10K2.u7881 (nat_lit 130991443) (nat_lit 10511612314) (nat_lit 0) A10K2.u7882 from rfl, allE_node, arows7881, irow7883, arows7882]
  all_goals rfl

theorem atot7883 : totK PA10K2 A10K2.u7883 = [0, 0, 588716830688, 3589287473215, 7790320855684, 6256950413730, 1315818074990, 57844007927, 0, 0] := by
  rw [show A10K2.u7883 = KTree.node A10K2.u7881 (nat_lit 130991443) (nat_lit 10511612314) (nat_lit 0) A10K2.u7882 from rfl, totK_node, atot7881, atot7882]
  decide +kernel

theorem arows7886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7886 = true := by
  rw [show A10K2.u7886 = KTree.node A10K2.u7884 (nat_lit 131017970) (nat_lit 14990917596) (nat_lit 0) A10K2.u7885 from rfl, allE_node, arows7884, irow7886, arows7885]
  all_goals rfl

theorem atot7886 : totK PA10K2 A10K2.u7886 = [0, 0, 1048814664328, 4933079787916, 8025112980082, 4934772969307, 870427761488, 25718713057, 0, 0] := by
  rw [show A10K2.u7886 = KTree.node A10K2.u7884 (nat_lit 131017970) (nat_lit 14990917596) (nat_lit 0) A10K2.u7885 from rfl, totK_node, atot7884, atot7885]
  decide +kernel

theorem arows7890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7890 = true := by
  rw [show A10K2.u7890 = KTree.node A10K2.u7888 (nat_lit 131036311) (nat_lit 13759458355) (nat_lit 0) A10K2.u7889 from rfl, allE_node, arows7888, irow7890, arows7889]
  all_goals rfl

theorem atot7890 : totK PA10K2 A10K2.u7890 = [0, 470692968618, 2135710762819, 4846321447897, 6767326351466, 4562191537231, 1055077078381, 62382159641, 0, 0] := by
  rw [show A10K2.u7890 = KTree.node A10K2.u7888 (nat_lit 131036311) (nat_lit 13759458355) (nat_lit 0) A10K2.u7889 from rfl, totK_node, atot7888, atot7889]
  decide +kernel

theorem arows7893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7893 = true := by
  rw [show A10K2.u7893 = KTree.node A10K2.u7891 (nat_lit 131603571) (nat_lit 5511017593) (nat_lit 0) A10K2.u7892 from rfl, allE_node, arows7891, irow7893, arows7892]
  all_goals rfl

theorem atot7893 : totK PA10K2 A10K2.u7893 = [0, 1061177434503, 5083182783250, 7881458549371, 4332640051059, 707334554818, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u7893 = KTree.node A10K2.u7891 (nat_lit 131603571) (nat_lit 5511017593) (nat_lit 0) A10K2.u7892 from rfl, totK_node, atot7891, atot7892]
  decide +kernel

theorem arows7899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7899 = true := by
  rw [show A10K2.u7899 = KTree.node A10K2.u7897 (nat_lit 131626226) (nat_lit 14998721644) (nat_lit 0) A10K2.u7898 from rfl, allE_node, arows7897, irow7899, arows7898]
  all_goals rfl

theorem atot7899 : totK PA10K2 A10K2.u7899 = [0, 540969523310, 3580949565596, 7832705672805, 6362927056753, 1561290152980, 88646843074, 0, 0, 0] := by
  rw [show A10K2.u7899 = KTree.node A10K2.u7897 (nat_lit 131626226) (nat_lit 14998721644) (nat_lit 0) A10K2.u7898 from rfl, totK_node, atot7897, atot7898]
  decide +kernel

theorem arows7902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7902 = true := by
  rw [show A10K2.u7902 = KTree.node A10K2.u7900 (nat_lit 131645700) (nat_lit 13036095526) (nat_lit 0) A10K2.u7901 from rfl, allE_node, arows7900, irow7902, arows7901]
  all_goals rfl

theorem atot7902 : totK PA10K2 A10K2.u7902 = [0, 0, 1185861678009, 5328869351048, 7858578279179, 4078968187534, 640395759443, 18459763130, 0, 0] := by
  rw [show A10K2.u7902 = KTree.node A10K2.u7900 (nat_lit 131645700) (nat_lit 13036095526) (nat_lit 0) A10K2.u7901 from rfl, totK_node, atot7900, atot7901]
  decide +kernel

theorem arows7906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7906 = true := by
  rw [show A10K2.u7906 = KTree.node A10K2.u7904 (nat_lit 131673088) (nat_lit 14584136153) (nat_lit 0) A10K2.u7905 from rfl, allE_node, arows7904, irow7906, arows7905]
  all_goals rfl

theorem atot7906 : totK PA10K2 A10K2.u7906 = [0, 853431600500, 4206814360085, 7576296552428, 5577683935203, 1403752175487, 89319918621, 0, 0, 0] := by
  rw [show A10K2.u7906 = KTree.node A10K2.u7904 (nat_lit 131673088) (nat_lit 14584136153) (nat_lit 0) A10K2.u7905 from rfl, totK_node, atot7904, atot7905]
  decide +kernel

theorem arows7909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7909 = true := by
  rw [show A10K2.u7909 = KTree.node A10K2.u7907 (nat_lit 131687713) (nat_lit 2342042682) (nat_lit 0) A10K2.u7908 from rfl, allE_node, arows7907, irow7909, arows7908]
  all_goals rfl

theorem atot7909 : totK PA10K2 A10K2.u7909 = [0, 1234919871936, 5584087993583, 8199178643703, 4264321685056, 646303116351, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u7909 = KTree.node A10K2.u7907 (nat_lit 131687713) (nat_lit 2342042682) (nat_lit 0) A10K2.u7908 from rfl, totK_node, atot7907, atot7908]
  decide +kernel

theorem arows7914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7914 = true := by
  rw [show A10K2.u7914 = KTree.node A10K2.u7912 (nat_lit 131706260) (nat_lit 8220109681) (nat_lit 0) A10K2.u7913 from rfl, allE_node, arows7912, irow7914, arows7913]
  all_goals rfl

theorem atot7914 : totK PA10K2 A10K2.u7914 = [0, 0, 1403258665812, 5801301795556, 7779761681815, 3785029744720, 592376939780, 18713227901, 0, 0] := by
  rw [show A10K2.u7914 = KTree.node A10K2.u7912 (nat_lit 131706260) (nat_lit 8220109681) (nat_lit 0) A10K2.u7913 from rfl, totK_node, atot7912, atot7913]
  decide +kernel

theorem arows7917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7917 = true := by
  rw [show A10K2.u7917 = KTree.node A10K2.u7915 (nat_lit 131720988) (nat_lit 11232066074) (nat_lit 0) A10K2.u7916 from rfl, allE_node, arows7915, irow7917, arows7916]
  all_goals rfl

theorem atot7917 : totK PA10K2 A10K2.u7917 = [0, 762038499923, 3409398930910, 6448393082989, 6412361281513, 2423798501216, 207764084126, 0, 0, 0] := by
  rw [show A10K2.u7917 = KTree.node A10K2.u7915 (nat_lit 131720988) (nat_lit 11232066074) (nat_lit 0) A10K2.u7916 from rfl, totK_node, atot7915, atot7916]
  decide +kernel

theorem arows7921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7921 = true := by
  rw [show A10K2.u7921 = KTree.node A10K2.u7919 (nat_lit 131802807) (nat_lit 14381767791) (nat_lit 0) A10K2.u7920 from rfl, allE_node, arows7919, irow7921, arows7920]
  all_goals rfl

theorem atot7921 : totK PA10K2 A10K2.u7921 = [0, 765763168051, 4417609049796, 8144797750533, 5202823332901, 992044802392, 47246161591, 0, 0, 0] := by
  rw [show A10K2.u7921 = KTree.node A10K2.u7919 (nat_lit 131802807) (nat_lit 14381767791) (nat_lit 0) A10K2.u7920 from rfl, totK_node, atot7919, atot7920]
  decide +kernel

theorem arows7924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7924 = true := by
  rw [show A10K2.u7924 = KTree.node A10K2.u7922 (nat_lit 131821156) (nat_lit 7267053164) (nat_lit 0) A10K2.u7923 from rfl, allE_node, arows7922, irow7924, arows7923]
  all_goals rfl

theorem atot7924 : totK PA10K2 A10K2.u7924 = [0, 896434737838, 4524785794610, 7906688308674, 5492978266931, 1248161882585, 62996513375, 0, 0, 0] := by
  rw [show A10K2.u7924 = KTree.node A10K2.u7922 (nat_lit 131821156) (nat_lit 7267053164) (nat_lit 0) A10K2.u7923 from rfl, totK_node, atot7922, atot7923]
  decide +kernel

theorem arows7933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7933 = true := by
  rw [show A10K2.u7933 = KTree.node A10K2.u7931 (nat_lit 131830385) (nat_lit 7409732089) (nat_lit 0) A10K2.u7932 from rfl, allE_node, arows7931, irow7933, arows7932]
  all_goals rfl

theorem atot7933 : totK PA10K2 A10K2.u7933 = [0, 0, 1498020417219, 6216469885805, 8063108243481, 3425719266588, 377953730479, 6904928264, 0, 0] := by
  rw [show A10K2.u7933 = KTree.node A10K2.u7931 (nat_lit 131830385) (nat_lit 7409732089) (nat_lit 0) A10K2.u7932 from rfl, totK_node, atot7931, atot7932]
  decide +kernel

theorem arows7936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7936 = true := by
  rw [show A10K2.u7936 = KTree.node A10K2.u7934 (nat_lit 131851740) (nat_lit 4891738487) (nat_lit 0) A10K2.u7935 from rfl, allE_node, arows7934, irow7936, arows7935]
  all_goals rfl

theorem atot7936 : totK PA10K2 A10K2.u7936 = [0, 0, 895145480297, 4772971375140, 8288772108598, 5094598418415, 788284083642, 19271132487, 0, 0] := by
  rw [show A10K2.u7936 = KTree.node A10K2.u7934 (nat_lit 131851740) (nat_lit 4891738487) (nat_lit 0) A10K2.u7935 from rfl, totK_node, atot7934, atot7935]
  decide +kernel

theorem arows7940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7940 = true := by
  rw [show A10K2.u7940 = KTree.node A10K2.u7938 (nat_lit 131862003) (nat_lit 7946139412) (nat_lit 0) A10K2.u7939 from rfl, allE_node, arows7938, irow7940, arows7939]
  all_goals rfl

theorem atot7940 : totK PA10K2 A10K2.u7940 = [0, 0, 1077977140266, 4810573442229, 7498788554022, 4734398958587, 1088103528713, 67355932906, 0, 0] := by
  rw [show A10K2.u7940 = KTree.node A10K2.u7938 (nat_lit 131862003) (nat_lit 7946139412) (nat_lit 0) A10K2.u7939 from rfl, totK_node, atot7938, atot7939]
  decide +kernel

theorem arows7943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7943 = true := by
  rw [show A10K2.u7943 = KTree.node A10K2.u7941 (nat_lit 131884773) (nat_lit 4665845997) (nat_lit 0) A10K2.u7942 from rfl, allE_node, arows7941, irow7943, arows7942]
  all_goals rfl

theorem atot7943 : totK PA10K2 A10K2.u7943 = [0, 0, 1000990837924, 5131931860440, 8442078293733, 4678101039859, 678055911038, 13229391832, 0, 0] := by
  rw [show A10K2.u7943 = KTree.node A10K2.u7941 (nat_lit 131884773) (nat_lit 4665845997) (nat_lit 0) A10K2.u7942 from rfl, totK_node, atot7941, atot7942]
  decide +kernel

theorem arows7948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7948 = true := by
  rw [show A10K2.u7948 = KTree.node A10K2.u7946 (nat_lit 131895302) (nat_lit 14686893806) (nat_lit 0) A10K2.u7947 from rfl, allE_node, arows7946, irow7948, arows7947]
  all_goals rfl

theorem atot7948 : totK PA10K2 A10K2.u7948 = [0, 0, 0, 1475470360373, 6242946946450, 7977779992140, 3092931168176, 334273687700, 7007974415, 0] := by
  rw [show A10K2.u7948 = KTree.node A10K2.u7946 (nat_lit 131895302) (nat_lit 14686893806) (nat_lit 0) A10K2.u7947 from rfl, totK_node, atot7946, atot7947]
  decide +kernel

theorem arows7951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7951 = true := by
  rw [show A10K2.u7951 = KTree.node A10K2.u7949 (nat_lit 131934103) (nat_lit 14220573112) (nat_lit 0) A10K2.u7950 from rfl, allE_node, arows7949, irow7951, arows7950]
  all_goals rfl

theorem atot7951 : totK PA10K2 A10K2.u7951 = [0, 0, 810541816207, 4082979600937, 7534673202304, 5767658785714, 1478295480729, 87512593487, 0, 0] := by
  rw [show A10K2.u7951 = KTree.node A10K2.u7949 (nat_lit 131934103) (nat_lit 14220573112) (nat_lit 0) A10K2.u7950 from rfl, totK_node, atot7949, atot7950]
  decide +kernel

theorem arows7955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7955 = true := by
  rw [show A10K2.u7955 = KTree.node A10K2.u7953 (nat_lit 131948958) (nat_lit 15558691728) (nat_lit 0) A10K2.u7954 from rfl, allE_node, arows7953, irow7955, arows7954]
  all_goals rfl

theorem atot7955 : totK PA10K2 A10K2.u7955 = [0, 0, 1275812037487, 5749627267767, 8301736807687, 4105473946833, 521248743858, 6279851884, 0, 0] := by
  rw [show A10K2.u7955 = KTree.node A10K2.u7953 (nat_lit 131948958) (nat_lit 15558691728) (nat_lit 0) A10K2.u7954 from rfl, totK_node, atot7953, atot7954]
  decide +kernel

theorem arows7958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7958 = true := by
  rw [show A10K2.u7958 = KTree.node A10K2.u7956 (nat_lit 131967532) (nat_lit 7633665360) (nat_lit 0) A10K2.u7957 from rfl, allE_node, arows7956, irow7958, arows7957]
  all_goals rfl

theorem atot7958 : totK PA10K2 A10K2.u7958 = [0, 0, 0, 1538329330745, 6328926976963, 8076014995848, 3264860818987, 349253301104, 7151180950, 0] := by
  rw [show A10K2.u7958 = KTree.node A10K2.u7956 (nat_lit 131967532) (nat_lit 7633665360) (nat_lit 0) A10K2.u7957 from rfl, totK_node, atot7956, atot7957]
  decide +kernel

theorem arows7964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7964 = true := by
  rw [show A10K2.u7964 = KTree.node A10K2.u7962 (nat_lit 131985407) (nat_lit 13968960306) (nat_lit 0) A10K2.u7963 from rfl, allE_node, arows7962, irow7964, arows7963]
  all_goals rfl

theorem atot7964 : totK PA10K2 A10K2.u7964 = [0, 0, 761537111178, 4117097320111, 7734961494074, 5731914198778, 1429023099253, 80939540425, 0, 0] := by
  rw [show A10K2.u7964 = KTree.node A10K2.u7962 (nat_lit 131985407) (nat_lit 13968960306) (nat_lit 0) A10K2.u7963 from rfl, totK_node, atot7962, atot7963]
  decide +kernel

theorem arows7967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7967 = true := by
  rw [show A10K2.u7967 = KTree.node A10K2.u7965 (nat_lit 132066881) (nat_lit 9899585383) (nat_lit 0) A10K2.u7966 from rfl, allE_node, arows7965, irow7967, arows7966]
  all_goals rfl

theorem atot7967 : totK PA10K2 A10K2.u7967 = [0, 0, 1045977270905, 5050423436698, 8130073644242, 4730141992657, 685329243851, 12219140272, 0, 0] := by
  rw [show A10K2.u7967 = KTree.node A10K2.u7965 (nat_lit 132066881) (nat_lit 9899585383) (nat_lit 0) A10K2.u7966 from rfl, totK_node, atot7965, atot7966]
  decide +kernel

theorem arows7971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7971 = true := by
  rw [show A10K2.u7971 = KTree.node A10K2.u7969 (nat_lit 132085121) (nat_lit 8747403692) (nat_lit 0) A10K2.u7970 from rfl, allE_node, arows7969, irow7971, arows7970]
  all_goals rfl

theorem atot7971 : totK PA10K2 A10K2.u7971 = [0, 0, 613737279027, 3787180886740, 7873215799394, 6153849958120, 1420024708698, 74831038383, 0, 0] := by
  rw [show A10K2.u7971 = KTree.node A10K2.u7969 (nat_lit 132085121) (nat_lit 8747403692) (nat_lit 0) A10K2.u7970 from rfl, totK_node, atot7969, atot7970]
  decide +kernel

theorem arows7974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7974 = true := by
  rw [show A10K2.u7974 = KTree.node A10K2.u7972 (nat_lit 132097927) (nat_lit 14096367277) (nat_lit 0) A10K2.u7973 from rfl, allE_node, arows7972, irow7974, arows7973]
  all_goals rfl

theorem atot7974 : totK PA10K2 A10K2.u7974 = [0, 0, 0, 1003505114074, 5237715173791, 8465508089919, 4415364229407, 562023865101, 12758098799, 0] := by
  rw [show A10K2.u7974 = KTree.node A10K2.u7972 (nat_lit 132097927) (nat_lit 14096367277) (nat_lit 0) A10K2.u7973 from rfl, totK_node, atot7972, atot7973]
  decide +kernel

theorem arows7979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7979 = true := by
  rw [show A10K2.u7979 = KTree.node A10K2.u7977 (nat_lit 132117034) (nat_lit 271385134) (nat_lit 0) A10K2.u7978 from rfl, allE_node, arows7977, irow7979, arows7978]
  all_goals rfl

theorem atot7979 : totK PA10K2 A10K2.u7979 = [0, 0, 396273731552, 2005688859962, 5090688005248, 6846066095950, 4307140155115, 983297972169, 61018386929, 0] := by
  rw [show A10K2.u7979 = KTree.node A10K2.u7977 (nat_lit 132117034) (nat_lit 271385134) (nat_lit 0) A10K2.u7978 from rfl, totK_node, atot7977, atot7978]
  decide +kernel

theorem arows7982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7982 = true := by
  rw [show A10K2.u7982 = KTree.node A10K2.u7980 (nat_lit 132127281) (nat_lit 9852288148) (nat_lit 0) A10K2.u7981 from rfl, allE_node, arows7980, irow7982, arows7981]
  all_goals rfl

theorem atot7982 : totK PA10K2 A10K2.u7982 = [0, 0, 1033174988750, 5177842432011, 7968007362732, 4136986124054, 689645701990, 30831673886, 0, 0] := by
  rw [show A10K2.u7982 = KTree.node A10K2.u7980 (nat_lit 132127281) (nat_lit 9852288148) (nat_lit 0) A10K2.u7981 from rfl, totK_node, atot7980, atot7981]
  decide +kernel

theorem arows7986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7986 = true := by
  rw [show A10K2.u7986 = KTree.node A10K2.u7984 (nat_lit 132149292) (nat_lit 11269734229) (nat_lit 0) A10K2.u7985 from rfl, allE_node, arows7984, irow7986, arows7985]
  all_goals rfl

theorem atot7986 : totK PA10K2 A10K2.u7986 = [0, 0, 802361088133, 4198050684388, 7768101855122, 5682208495778, 1407328935612, 88895808710, 0, 0] := by
  rw [show A10K2.u7986 = KTree.node A10K2.u7984 (nat_lit 132149292) (nat_lit 11269734229) (nat_lit 0) A10K2.u7985 from rfl, totK_node, atot7984, atot7985]
  decide +kernel

theorem arows7989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7989 = true := by
  rw [show A10K2.u7989 = KTree.node A10K2.u7987 (nat_lit 132159773) (nat_lit 6182573251) (nat_lit 0) A10K2.u7988 from rfl, allE_node, arows7987, irow7989, arows7988]
  all_goals rfl

theorem atot7989 : totK PA10K2 A10K2.u7989 = [0, 0, 0, 1107258188990, 5431260544654, 8066921712569, 3772623026051, 517111501981, 13364899180, 0] := by
  rw [show A10K2.u7989 = KTree.node A10K2.u7987 (nat_lit 132159773) (nat_lit 6182573251) (nat_lit 0) A10K2.u7988 from rfl, totK_node, atot7987, atot7988]
  decide +kernel

theorem arows7996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7996 = true := by
  rw [show A10K2.u7996 = KTree.node A10K2.u7994 (nat_lit 132252095) (nat_lit 14060124258) (nat_lit 0) A10K2.u7995 from rfl, allE_node, arows7994, irow7996, arows7995]
  all_goals rfl

theorem atot7996 : totK PA10K2 A10K2.u7996 = [0, 0, 759554354984, 4051154075234, 7554795385197, 5770783989897, 1573717943417, 107445153660, 0, 0] := by
  rw [show A10K2.u7996 = KTree.node A10K2.u7994 (nat_lit 132252095) (nat_lit 14060124258) (nat_lit 0) A10K2.u7995 from rfl, totK_node, atot7994, atot7995]
  decide +kernel

theorem arows7999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7999 = true := by
  rw [show A10K2.u7999 = KTree.node A10K2.u7997 (nat_lit 132285004) (nat_lit 10617068230) (nat_lit 0) A10K2.u7998 from rfl, allE_node, arows7997, irow7999, arows7998]
  all_goals rfl

theorem atot7999 : totK PA10K2 A10K2.u7999 = [0, 0, 556534364705, 3608857816096, 7836210068245, 5983688087730, 1199218684888, 49285645620, 0, 0] := by
  rw [show A10K2.u7999 = KTree.node A10K2.u7997 (nat_lit 132285004) (nat_lit 10617068230) (nat_lit 0) A10K2.u7998 from rfl, totK_node, atot7997, atot7998]
  decide +kernel

theorem arows8003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8003 = true := by
  rw [show A10K2.u8003 = KTree.node A10K2.u8001 (nat_lit 132321799) (nat_lit 12505225686) (nat_lit 0) A10K2.u8002 from rfl, allE_node, arows8001, irow8003, arows8002]
  all_goals rfl

theorem atot8003 : totK PA10K2 A10K2.u8003 = [0, 0, 1383966611651, 5802990605998, 7967856899272, 3949260519161, 673640155651, 24813634511, 0, 0] := by
  rw [show A10K2.u8003 = KTree.node A10K2.u8001 (nat_lit 132321799) (nat_lit 12505225686) (nat_lit 0) A10K2.u8002 from rfl, totK_node, atot8001, atot8002]
  decide +kernel

theorem arows8006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8006 = true := by
  rw [show A10K2.u8006 = KTree.node A10K2.u8004 (nat_lit 132343706) (nat_lit 14875845437) (nat_lit 0) A10K2.u8005 from rfl, allE_node, arows8004, irow8006, arows8005]
  all_goals rfl

theorem atot8006 : totK PA10K2 A10K2.u8006 = [0, 0, 868494622419, 4645067349735, 8234945078958, 5282237914754, 943730070300, 26497647239, 0, 0] := by
  rw [show A10K2.u8006 = KTree.node A10K2.u8004 (nat_lit 132343706) (nat_lit 14875845437) (nat_lit 0) A10K2.u8005 from rfl, totK_node, atot8004, atot8005]
  decide +kernel

theorem arows8011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8011 = true := by
  rw [show A10K2.u8011 = KTree.node A10K2.u8009 (nat_lit 132354006) (nat_lit 15605321001) (nat_lit 0) A10K2.u8010 from rfl, allE_node, arows8009, irow8011, arows8010]
  all_goals rfl

theorem atot8011 : totK PA10K2 A10K2.u8011 = [0, 0, 0, 1428622408339, 6162702681444, 8282876494638, 3572572201961, 387411764461, 6904928264, 0] := by
  rw [show A10K2.u8011 = KTree.node A10K2.u8009 (nat_lit 132354006) (nat_lit 15605321001) (nat_lit 0) A10K2.u8010 from rfl, totK_node, atot8009, atot8010]
  decide +kernel

theorem arows8014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8014 = true := by
  rw [show A10K2.u8014 = KTree.node A10K2.u8012 (nat_lit 132376275) (nat_lit 10678812061) (nat_lit 0) A10K2.u8013 from rfl, allE_node, arows8012, irow8014, arows8013]
  all_goals rfl

theorem atot8014 : totK PA10K2 A10K2.u8014 = [0, 0, 0, 867694288916, 4728390320811, 8357051424815, 5094815147475, 759270629087, 18990462437, 0] := by
  rw [show A10K2.u8014 = KTree.node A10K2.u8012 (nat_lit 132376275) (nat_lit 10678812061) (nat_lit 0) A10K2.u8013 from rfl, totK_node, atot8012, atot8013]
  decide +kernel

theorem arows8018 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8018 = true := by
  rw [show A10K2.u8018 = KTree.node A10K2.u8016 (nat_lit 132386367) (nat_lit 14111345449) (nat_lit 0) A10K2.u8017 from rfl, allE_node, arows8016, irow8018, arows8017]
  all_goals rfl

theorem atot8018 : totK PA10K2 A10K2.u8018 = [0, 0, 0, 1134775994759, 4953718947782, 7568819785202, 4613229468605, 1019892174589, 62250918251, 0] := by
  rw [show A10K2.u8018 = KTree.node A10K2.u8016 (nat_lit 132386367) (nat_lit 14111345449) (nat_lit 0) A10K2.u8017 from rfl, totK_node, atot8016, atot8017]
  decide +kernel

theorem arows8021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8021 = true := by
  rw [show A10K2.u8021 = KTree.node A10K2.u8019 (nat_lit 132408819) (nat_lit 8612695242) (nat_lit 0) A10K2.u8020 from rfl, allE_node, arows8019, irow8021, arows8020]
  all_goals rfl

theorem atot8021 : totK PA10K2 A10K2.u8021 = [0, 0, 0, 1097033813676, 5461148092225, 8400527121540, 4222155919780, 508893067474, 6853348008, 0] := by
  rw [show A10K2.u8021 = KTree.node A10K2.u8019 (nat_lit 132408819) (nat_lit 8612695242) (nat_lit 0) A10K2.u8020 from rfl, totK_node, atot8019, atot8020]
  decide +kernel

theorem arows8027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8027 = true := by
  rw [show A10K2.u8027 = KTree.node A10K2.u8025 (nat_lit 132420038) (nat_lit 14875546244) (nat_lit 0) A10K2.u8026 from rfl, allE_node, arows8025, irow8027, arows8026]
  all_goals rfl

theorem atot8027 : totK PA10K2 A10K2.u8027 = [0, 0, 0, 0, 1777056305855, 6787699491475, 7673142819362, 2736926706476, 295676438318, 7237400819] := by
  rw [show A10K2.u8027 = KTree.node A10K2.u8025 (nat_lit 132420038) (nat_lit 14875546244) (nat_lit 0) A10K2.u8026 from rfl, totK_node, atot8025, atot8026]
  decide +kernel

theorem arows8030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8030 = true := by
  rw [show A10K2.u8030 = KTree.node A10K2.u8028 (nat_lit 132517375) (nat_lit 10700386624) (nat_lit 0) A10K2.u8029 from rfl, allE_node, arows8028, irow8030, arows8029]
  all_goals rfl

theorem atot8030 : totK PA10K2 A10K2.u8030 = [0, 0, 0, 1430762851388, 6168545899237, 7970207537641, 3435942505019, 520039117133, 29010686974, 0] := by
  rw [show A10K2.u8030 = KTree.node A10K2.u8028 (nat_lit 132517375) (nat_lit 10700386624) (nat_lit 0) A10K2.u8029 from rfl, totK_node, atot8028, atot8029]
  decide +kernel

theorem arows8034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8034 = true := by
  rw [show A10K2.u8034 = KTree.node A10K2.u8032 (nat_lit 132584228) (nat_lit 13123625433) (nat_lit 0) A10K2.u8033 from rfl, allE_node, arows8032, irow8034, arows8033]
  all_goals rfl

theorem atot8034 : totK PA10K2 A10K2.u8034 = [0, 0, 0, 1268140165065, 5835862667132, 8301219062085, 3877798997120, 474093336665, 12473006693, 0] := by
  rw [show A10K2.u8034 = KTree.node A10K2.u8032 (nat_lit 132584228) (nat_lit 13123625433) (nat_lit 0) A10K2.u8033 from rfl, totK_node, atot8032, atot8033]
  decide +kernel

theorem arows8037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8037 = true := by
  rw [show A10K2.u8037 = KTree.node A10K2.u8035 (nat_lit 132607472) (nat_lit 13921770426) (nat_lit 0) A10K2.u8036 from rfl, allE_node, arows8035, irow8037, arows8036]
  all_goals rfl

theorem atot8037 : totK PA10K2 A10K2.u8037 = [0, 0, 0, 868494622419, 4393779661054, 7953633849243, 5557411516272, 1135633782342, 37540485659, 0] := by
  rw [show A10K2.u8037 = KTree.node A10K2.u8035 (nat_lit 132607472) (nat_lit 13921770426) (nat_lit 0) A10K2.u8036 from rfl, totK_node, atot8035, atot8036]
  decide +kernel

theorem arows8042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8042 = true := by
  rw [show A10K2.u8042 = KTree.node A10K2.u8040 (nat_lit 132724072) (nat_lit 7034832340) (nat_lit 0) A10K2.u8041 from rfl, allE_node, arows8040, irow8042, arows8041]
  all_goals rfl

theorem atot8042 : totK PA10K2 A10K2.u8042 = [0, 0, 1335397954408, 5522484503066, 7650585743534, 3988861479278, 729913454314, 147494323447, 31688522620, 0] := by
  rw [show A10K2.u8042 = KTree.node A10K2.u8040 (nat_lit 132724072) (nat_lit 7034832340) (nat_lit 0) A10K2.u8041 from rfl, totK_node, atot8040, atot8041]
  decide +kernel

theorem arows8045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8045 = true := by
  rw [show A10K2.u8045 = KTree.node A10K2.u8043 (nat_lit 132736955) (nat_lit 7032327865) (nat_lit 0) A10K2.u8044 from rfl, allE_node, arows8043, irow8045, arows8044]
  all_goals rfl

theorem atot8045 : totK PA10K2 A10K2.u8045 = [0, 0, 902749937624, 4831820599433, 8309943714587, 4922028742949, 864543319610, 25377674688, 0, 0] := by
  rw [show A10K2.u8045 = KTree.node A10K2.u8043 (nat_lit 132736955) (nat_lit 7032327865) (nat_lit 0) A10K2.u8044 from rfl, totK_node, atot8043, atot8044]
  decide +kernel

theorem arows8049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8049 = true := by
  rw [show A10K2.u8049 = KTree.node A10K2.u8047 (nat_lit 132756653) (nat_lit 6117780252) (nat_lit 0) A10K2.u8048 from rfl, allE_node, arows8047, irow8049, arows8048]
  all_goals rfl

theorem atot8049 : totK PA10K2 A10K2.u8049 = [0, 0, 0, 1353449006873, 5688398569435, 7895583612756, 3850356088918, 548486365739, 13576218110, 0] := by
  rw [show A10K2.u8049 = KTree.node A10K2.u8047 (nat_lit 132756653) (nat_lit 6117780252) (nat_lit 0) A10K2.u8048 from rfl, totK_node, atot8047, atot8048]
  decide +kernel

theorem arows8052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8052 = true := by
  rw [show A10K2.u8052 = KTree.node A10K2.u8050 (nat_lit 132771201) (nat_lit 9052370070) (nat_lit 0) A10K2.u8051 from rfl, allE_node, arows8050, irow8052, arows8051]
  all_goals rfl

theorem atot8052 : totK PA10K2 A10K2.u8052 = [0, 0, 762716802215, 3661927149160, 7043678936917, 6223417702826, 1979881324961, 134108628927, 0, 0] := by
  rw [show A10K2.u8052 = KTree.node A10K2.u8050 (nat_lit 132771201) (nat_lit 9052370070) (nat_lit 0) A10K2.u8051 from rfl, totK_node, atot8050, atot8051]
  decide +kernel

theorem arows8060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8060 = true := by
  rw [show A10K2.u8060 = KTree.node A10K2.u8058 (nat_lit 132794595) (nat_lit 10340699668) (nat_lit 0) A10K2.u8059 from rfl, allE_node, arows8058, irow8060, arows8059]
  all_goals rfl

theorem atot8060 : totK PA10K2 A10K2.u8060 = [0, 0, 558354638208, 3757792572828, 7879293557630, 5923818529433, 1379851850287, 70888066973, 0, 0] := by
  rw [show A10K2.u8060 = KTree.node A10K2.u8058 (nat_lit 132794595) (nat_lit 10340699668) (nat_lit 0) A10K2.u8059 from rfl, totK_node, atot8058, atot8059]
  decide +kernel

theorem arows8063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8063 = true := by
  rw [show A10K2.u8063 = KTree.node A10K2.u8061 (nat_lit 132845959) (nat_lit 14322147822) (nat_lit 0) A10K2.u8062 from rfl, allE_node, arows8061, irow8063, arows8062]
  all_goals rfl

theorem atot8063 : totK PA10K2 A10K2.u8063 = [0, 0, 1384971655032, 5774491570416, 8003255102071, 4059543902023, 618088539359, 18818389076, 0, 0] := by
  rw [show A10K2.u8063 = KTree.node A10K2.u8061 (nat_lit 132845959) (nat_lit 14322147822) (nat_lit 0) A10K2.u8062 from rfl, totK_node, atot8061, atot8062]
  decide +kernel

theorem arows8067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8067 = true := by
  rw [show A10K2.u8067 = KTree.node A10K2.u8065 (nat_lit 132866974) (nat_lit 15179368968) (nat_lit 0) A10K2.u8066 from rfl, allE_node, arows8065, irow8067, arows8066]
  all_goals rfl

theorem atot8067 : totK PA10K2 A10K2.u8067 = [0, 0, 868650652504, 4684190891498, 8243107861972, 5128879384313, 891738175170, 25564086650, 0, 0] := by
  rw [show A10K2.u8067 = KTree.node A10K2.u8065 (nat_lit 132866974) (nat_lit 15179368968) (nat_lit 0) A10K2.u8066 from rfl, totK_node, atot8065, atot8066]
  decide +kernel

theorem arows8070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8070 = true := by
  rw [show A10K2.u8070 = KTree.node A10K2.u8068 (nat_lit 132877980) (nat_lit 8155982921) (nat_lit 0) A10K2.u8069 from rfl, allE_node, arows8068, irow8070, arows8069]
  all_goals rfl

theorem atot8070 : totK PA10K2 A10K2.u8070 = [0, 0, 0, 1551565639398, 6388096144834, 8229305551650, 3431090602313, 363579741703, 6632180018, 0] := by
  rw [show A10K2.u8070 = KTree.node A10K2.u8068 (nat_lit 132877980) (nat_lit 8155982921) (nat_lit 0) A10K2.u8069 from rfl, totK_node, atot8068, atot8069]
  decide +kernel

theorem arows8075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8075 = true := by
  rw [show A10K2.u8075 = KTree.node A10K2.u8073 (nat_lit 132899432) (nat_lit 11169042827) (nat_lit 0) A10K2.u8074 from rfl, allE_node, arows8073, irow8075, arows8074]
  all_goals rfl

theorem atot8075 : totK PA10K2 A10K2.u8075 = [0, 0, 0, 1095350513927, 5342854385252, 8332607799916, 4465798387706, 588215384174, 13113983930, 0] := by
  rw [show A10K2.u8075 = KTree.node A10K2.u8073 (nat_lit 132899432) (nat_lit 11169042827) (nat_lit 0) A10K2.u8074 from rfl, totK_node, atot8073, atot8074]
  decide +kernel

theorem arows8078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8078 = true := by
  rw [show A10K2.u8078 = KTree.node A10K2.u8076 (nat_lit 132983474) (nat_lit 15019370566) (nat_lit 0) A10K2.u8077 from rfl, allE_node, arows8076, irow8078, arows8077]
  all_goals rfl

theorem atot8078 : totK PA10K2 A10K2.u8078 = [0, 0, 0, 845134994565, 4375757042346, 7764061914655, 5320156745479, 1189921447968, 68619385738, 0] := by
  rw [show A10K2.u8078 = KTree.node A10K2.u8076 (nat_lit 132983474) (nat_lit 15019370566) (nat_lit 0) A10K2.u8077 from rfl, totK_node, atot8076, atot8077]
  decide +kernel

theorem arows8082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8082 = true := by
  rw [show A10K2.u8082 = KTree.node A10K2.u8080 (nat_lit 132998073) (nat_lit 6942798429) (nat_lit 0) A10K2.u8081 from rfl, allE_node, arows8080, irow8082, arows8081]
  all_goals rfl

theorem atot8082 : totK PA10K2 A10K2.u8082 = [0, 0, 0, 1385728585392, 5950490816787, 8229102813979, 3803253640616, 438832840997, 6962742351, 0] := by
  rw [show A10K2.u8082 = KTree.node A10K2.u8080 (nat_lit 132998073) (nat_lit 6942798429) (nat_lit 0) A10K2.u8081 from rfl, totK_node, atot8080, atot8081]
  decide +kernel

theorem arows8085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8085 = true := by
  rw [show A10K2.u8085 = KTree.node A10K2.u8083 (nat_lit 133017042) (nat_lit 15196470988) (nat_lit 0) A10K2.u8084 from rfl, allE_node, arows8083, irow8085, arows8084]
  all_goals rfl

theorem atot8085 : totK PA10K2 A10K2.u8085 = [0, 0, 0, 0, 1833823559643, 6873982757152, 7688983475972, 2764860561585, 288765498240, 7380853412] := by
  rw [show A10K2.u8085 = KTree.node A10K2.u8083 (nat_lit 133017042) (nat_lit 15196470988) (nat_lit 0) A10K2.u8084 from rfl, totK_node, atot8083, atot8084]
  decide +kernel

theorem arows8091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8091 = true := by
  rw [show A10K2.u8091 = KTree.node A10K2.u8089 (nat_lit 133048576) (nat_lit 9241259697) (nat_lit 0) A10K2.u8090 from rfl, allE_node, arows8089, irow8091, arows8090]
  all_goals rfl

theorem atot8091 : totK PA10K2 A10K2.u8091 = [0, 0, 0, 1602554388878, 6134871377447, 7469668290186, 3782298829596, 763730021039, 43953344306, 0] := by
  rw [show A10K2.u8091 = KTree.node A10K2.u8089 (nat_lit 133048576) (nat_lit 9241259697) (nat_lit 0) A10K2.u8090 from rfl, totK_node, atot8089, atot8090]
  decide +kernel

theorem arows8094 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8094 = true := by
  rw [show A10K2.u8094 = KTree.node A10K2.u8092 (nat_lit 133113629) (nat_lit 6249161093) (nat_lit 0) A10K2.u8093 from rfl, allE_node, arows8092, irow8094, arows8093]
  all_goals rfl

theorem atot8094 : totK PA10K2 A10K2.u8094 = [0, 0, 0, 1096605235086, 5212499620214, 8234083770521, 4620957248205, 655982711230, 19417837436, 0] := by
  rw [show A10K2.u8094 = KTree.node A10K2.u8092 (nat_lit 133113629) (nat_lit 6249161093) (nat_lit 0) A10K2.u8093 from rfl, totK_node, atot8092, atot8093]
  decide +kernel

theorem arows8098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8098 = true := by
  rw [show A10K2.u8098 = KTree.node A10K2.u8096 (nat_lit 133132242) (nat_lit 14780197222) (nat_lit 0) A10K2.u8097 from rfl, allE_node, arows8096, irow8098, arows8097]
  all_goals rfl

theorem atot8098 : totK PA10K2 A10K2.u8098 = [0, 0, 310694887869, 1557667017829, 4583060847269, 7343665256350, 4958700313969, 1087262047949, 62382159641, 0] := by
  rw [show A10K2.u8098 = KTree.node A10K2.u8096 (nat_lit 133132242) (nat_lit 14780197222) (nat_lit 0) A10K2.u8097 from rfl, totK_node, atot8096, atot8097]
  decide +kernel

theorem arows8101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8101 = true := by
  rw [show A10K2.u8101 = KTree.node A10K2.u8099 (nat_lit 133699598) (nat_lit 12434362717) (nat_lit 0) A10K2.u8100 from rfl, allE_node, arows8099, irow8101, arows8100]
  all_goals rfl

theorem atot8101 : totK PA10K2 A10K2.u8101 = [0, 0, 1050774339767, 5308351548400, 8239815774344, 4048647188324, 609484391316, 18469913835, 0, 0] := by
  rw [show A10K2.u8101 = KTree.node A10K2.u8099 (nat_lit 133699598) (nat_lit 12434362717) (nat_lit 0) A10K2.u8100 from rfl, totK_node, atot8099, atot8100]
  decide +kernel

theorem arows8106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8106 = true := by
  rw [show A10K2.u8106 = KTree.node A10K2.u8104 (nat_lit 133722742) (nat_lit 15280770618) (nat_lit 0) A10K2.u8105 from rfl, allE_node, arows8104, irow8106, arows8105]
  all_goals rfl

theorem atot8106 : totK PA10K2 A10K2.u8106 = [0, 0, 719492328128, 4100136721164, 7857911557216, 5879413066002, 1458333081897, 81617060564, 0, 0] := by
  rw [show A10K2.u8106 = KTree.node A10K2.u8104 (nat_lit 133722742) (nat_lit 15280770618) (nat_lit 0) A10K2.u8105 from rfl, totK_node, atot8104, atot8105]
  decide +kernel

theorem arows8109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8109 = true := by
  rw [show A10K2.u8109 = KTree.node A10K2.u8107 (nat_lit 133742651) (nat_lit 1942873776) (nat_lit 0) A10K2.u8108 from rfl, allE_node, arows8107, irow8109, arows8108]
  all_goals rfl

theorem atot8109 : totK PA10K2 A10K2.u8109 = [0, 0, 0, 1246136764531, 5866102132625, 8248184273891, 3516943625887, 407520506529, 12477124820, 0] := by
  rw [show A10K2.u8109 = KTree.node A10K2.u8107 (nat_lit 133742651) (nat_lit 1942873776) (nat_lit 0) A10K2.u8108 from rfl, totK_node, atot8107, atot8108]
  decide +kernel

theorem arows8113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8113 = true := by
  rw [show A10K2.u8113 = KTree.node A10K2.u8111 (nat_lit 133770637) (nat_lit 1194836469) (nat_lit 0) A10K2.u8112 from rfl, allE_node, arows8111, irow8113, arows8112]
  all_goals rfl

theorem atot8113 : totK PA10K2 A10K2.u8113 = [0, 0, 1083871967757, 4744816578603, 7487002038437, 5034456441399, 1254440923284, 76274168032, 0, 0] := by
  rw [show A10K2.u8113 = KTree.node A10K2.u8111 (nat_lit 133770637) (nat_lit 1194836469) (nat_lit 0) A10K2.u8112 from rfl, totK_node, atot8111, atot8112]
  decide +kernel

theorem arows8116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8116 = true := by
  rw [show A10K2.u8116 = KTree.node A10K2.u8114 (nat_lit 133786675) (nat_lit 7031829568) (nat_lit 0) A10K2.u8115 from rfl, allE_node, arows8114, irow8116, arows8115]
  all_goals rfl

theorem atot8116 : totK PA10K2 A10K2.u8116 = [0, 0, 1004470456043, 5213149183349, 8541081505769, 4722755025357, 731198052762, 13814447077, 0, 0] := by
  rw [show A10K2.u8116 = KTree.node A10K2.u8114 (nat_lit 133786675) (nat_lit 7031829568) (nat_lit 0) A10K2.u8115 from rfl, totK_node, atot8114, atot8115]
  decide +kernel

theorem arows8123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8123 = true := by
  rw [show A10K2.u8123 = KTree.node A10K2.u8121 (nat_lit 133805296) (nat_lit 8044559346) (nat_lit 0) A10K2.u8122 from rfl, allE_node, arows8121, irow8123, arows8122]
  all_goals rfl

theorem atot8123 : totK PA10K2 A10K2.u8123 = [0, 0, 0, 1253688743439, 5675421448707, 8030824039081, 3798808025217, 469021213594, 12696458652, 0] := by
  rw [show A10K2.u8123 = KTree.node A10K2.u8121 (nat_lit 133805296) (nat_lit 8044559346) (nat_lit 0) A10K2.u8122 from rfl, totK_node, atot8121, atot8122]
  decide +kernel

theorem arows8126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8126 = true := by
  rw [show A10K2.u8126 = KTree.node A10K2.u8124 (nat_lit 133890119) (nat_lit 11090568428) (nat_lit 0) A10K2.u8125 from rfl, allE_node, arows8124, irow8126, arows8125]
  all_goals rfl

theorem atot8126 : totK PA10K2 A10K2.u8126 = [0, 0, 762038499923, 3914070993736, 7312805541120, 5962605855630, 1711802580864, 99489897944, 0, 0] := by
  rw [show A10K2.u8126 = KTree.node A10K2.u8124 (nat_lit 133890119) (nat_lit 11090568428) (nat_lit 0) A10K2.u8125 from rfl, totK_node, atot8124, atot8125]
  decide +kernel

theorem arows8130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8130 = true := by
  rw [show A10K2.u8130 = KTree.node A10K2.u8128 (nat_lit 133901973) (nat_lit 5564765879) (nat_lit 0) A10K2.u8129 from rfl, allE_node, arows8128, irow8130, arows8129]
  all_goals rfl

theorem atot8130 : totK PA10K2 A10K2.u8130 = [0, 0, 1046967458492, 5062513874972, 8109161366359, 4649819675246, 751007306150, 17754888877, 0, 0] := by
  rw [show A10K2.u8130 = KTree.node A10K2.u8128 (nat_lit 133901973) (nat_lit 5564765879) (nat_lit 0) A10K2.u8129 from rfl, totK_node, atot8128, atot8129]
  decide +kernel

theorem arows8133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8133 = true := by
  rw [show A10K2.u8133 = KTree.node A10K2.u8131 (nat_lit 133920099) (nat_lit 9059962635) (nat_lit 0) A10K2.u8132 from rfl, allE_node, arows8131, irow8133, arows8132]
  all_goals rfl

theorem atot8133 : totK PA10K2 A10K2.u8133 = [0, 0, 615230447397, 3715691843349, 7754046242682, 6177406017290, 1498330748289, 80537954553, 0, 0] := by
  rw [show A10K2.u8133 = KTree.node A10K2.u8131 (nat_lit 133920099) (nat_lit 9059962635) (nat_lit 0) A10K2.u8132 from rfl, totK_node, atot8131, atot8132]
  decide +kernel

theorem arows8138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8138 = true := by
  rw [show A10K2.u8138 = KTree.node A10K2.u8136 (nat_lit 133932728) (nat_lit 9353580640) (nat_lit 0) A10K2.u8137 from rfl, allE_node, arows8136, irow8138, arows8137]
  all_goals rfl

theorem atot8138 : totK PA10K2 A10K2.u8138 = [0, 0, 0, 965298635565, 5109125482122, 8418458401240, 4496718948716, 586338955257, 13951953716, 0] := by
  rw [show A10K2.u8138 = KTree.node A10K2.u8136 (nat_lit 133932728) (nat_lit 9353580640) (nat_lit 0) A10K2.u8137 from rfl, totK_node, atot8136, atot8137]
  decide +kernel

theorem arows8141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8141 = true := by
  rw [show A10K2.u8141 = KTree.node A10K2.u8139 (nat_lit 133951532) (nat_lit 8486655753) (nat_lit 0) A10K2.u8140 from rfl, allE_node, arows8139, irow8141, arows8140]
  all_goals rfl

theorem atot8141 : totK PA10K2 A10K2.u8141 = [0, 0, 0, 1204302547341, 5112976493073, 7617804234413, 4751454682217, 1031492345483, 61110126106, 0] := by
  rw [show A10K2.u8141 = KTree.node A10K2.u8139 (nat_lit 133951532) (nat_lit 8486655753) (nat_lit 0) A10K2.u8140 from rfl, totK_node, atot8139, atot8140]
  decide +kernel

theorem arows8145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8145 = true := by
  rw [show A10K2.u8145 = KTree.node A10K2.u8143 (nat_lit 133962020) (nat_lit 14146055856) (nat_lit 0) A10K2.u8144 from rfl, allE_node, arows8143, irow8145, arows8144]
  all_goals rfl

theorem atot8145 : totK PA10K2 A10K2.u8145 = [0, 0, 0, 1227182571944, 5539543284869, 8107738798021, 3940614663611, 475681074263, 12477124820, 0] := by
  rw [show A10K2.u8145 = KTree.node A10K2.u8143 (nat_lit 133962020) (nat_lit 14146055856) (nat_lit 0) A10K2.u8144 from rfl, totK_node, atot8143, atot8144]
  decide +kernel

theorem arows8148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8148 = true := by
  rw [show A10K2.u8148 = KTree.node A10K2.u8146 (nat_lit 133985949) (nat_lit 2972846462) (nat_lit 0) A10K2.u8147 from rfl, allE_node, arows8146, irow8148, arows8147]
  all_goals rfl

theorem atot8148 : totK PA10K2 A10K2.u8148 = [0, 0, 0, 537680587155, 3740351617852, 8066461504220, 6219524800239, 1366911388393, 74848461955, 0] := by
  rw [show A10K2.u8148 = KTree.node A10K2.u8146 (nat_lit 133985949) (nat_lit 2972846462) (nat_lit 0) A10K2.u8147 from rfl, totK_node, atot8146, atot8147]
  decide +kernel

theorem arows8154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8154 = true := by
  rw [show A10K2.u8154 = KTree.node A10K2.u8152 (nat_lit 134013362) (nat_lit 12734719087) (nat_lit 0) A10K2.u8153 from rfl, allE_node, arows8152, irow8154, arows8153]
  all_goals rfl

theorem atot8154 : totK PA10K2 A10K2.u8154 = [0, 0, 0, 310599358184, 2380919767083, 6569028008460, 7249068477677, 2721295601308, 299472978145, 6725424603] := by
  rw [show A10K2.u8154 = KTree.node A10K2.u8152 (nat_lit 134013362) (nat_lit 12734719087) (nat_lit 0) A10K2.u8153 from rfl, totK_node, atot8152, atot8153]
  decide +kernel

theorem arows8157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8157 = true := by
  rw [show A10K2.u8157 = KTree.node A10K2.u8155 (nat_lit 134036691) (nat_lit 10767672975) (nat_lit 0) A10K2.u8156 from rfl, allE_node, arows8155, irow8157, arows8156]
  all_goals rfl

theorem atot8157 : totK PA10K2 A10K2.u8157 = [0, 0, 0, 1449755114794, 6009159979046, 7982923935463, 3813720918456, 466499420067, 12696458652, 0] := by
  rw [show A10K2.u8157 = KTree.node A10K2.u8155 (nat_lit 134036691) (nat_lit 10767672975) (nat_lit 0) A10K2.u8156 from rfl, totK_node, atot8155, atot8156]
  decide +kernel

theorem arows8161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8161 = true := by
  rw [show A10K2.u8161 = KTree.node A10K2.u8159 (nat_lit 134053083) (nat_lit 8567730037) (nat_lit 0) A10K2.u8160 from rfl, allE_node, arows8159, irow8161, arows8160]
  all_goals rfl

theorem atot8161 : totK PA10K2 A10K2.u8161 = [0, 0, 0, 321051690767, 3019487388857, 7772342353136, 7004487494589, 1777488453567, 87866663686, 0] := by
  rw [show A10K2.u8161 = KTree.node A10K2.u8159 (nat_lit 134053083) (nat_lit 8567730037) (nat_lit 0) A10K2.u8160 from rfl, totK_node, atot8159, atot8160]
  decide +kernel

theorem arows8164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8164 = true := by
  rw [show A10K2.u8164 = KTree.node A10K2.u8162 (nat_lit 134080156) (nat_lit 10761408266) (nat_lit 0) A10K2.u8163 from rfl, allE_node, arows8162, irow8164, arows8163]
  all_goals rfl

theorem atot8164 : totK PA10K2 A10K2.u8164 = [0, 0, 0, 711321896246, 3465771547116, 6541683902276, 6160304086949, 2398825277253, 297815609343, 6860445330] := by
  rw [show A10K2.u8164 = KTree.node A10K2.u8162 (nat_lit 134080156) (nat_lit 10761408266) (nat_lit 0) A10K2.u8163 from rfl, totK_node, atot8162, atot8163]
  decide +kernel

theorem arows8169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8169 = true := by
  rw [show A10K2.u8169 = KTree.node A10K2.u8167 (nat_lit 134162142) (nat_lit 10311406266) (nat_lit 0) A10K2.u8168 from rfl, allE_node, arows8167, irow8169, arows8168]
  all_goals rfl

theorem atot8169 : totK PA10K2 A10K2.u8169 = [0, 0, 0, 805580165028, 4583712968159, 8191280237820, 5014080896493, 756489904888, 23612865148, 0] := by
  rw [show A10K2.u8169 = KTree.node A10K2.u8167 (nat_lit 134162142) (nat_lit 10311406266) (nat_lit 0) A10K2.u8168 from rfl, totK_node, atot8167, atot8168]
  decide +kernel

theorem arows8172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8172 = true := by
  rw [show A10K2.u8172 = KTree.node A10K2.u8170 (nat_lit 134180800) (nat_lit 14627760404) (nat_lit 0) A10K2.u8171 from rfl, allE_node, arows8170, irow8172, arows8171]
  all_goals rfl

theorem atot8172 : totK PA10K2 A10K2.u8172 = [0, 0, 0, 890887868445, 4542875357489, 7896875725205, 5300436332874, 1130299718316, 62833682686, 0] := by
  rw [show A10K2.u8172 = KTree.node A10K2.u8170 (nat_lit 134180800) (nat_lit 14627760404) (nat_lit 0) A10K2.u8171 from rfl, totK_node, atot8170, atot8171]
  decide +kernel

theorem arows8176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8176 = true := by
  rw [show A10K2.u8176 = KTree.node A10K2.u8174 (nat_lit 134192310) (nat_lit 16533336620) (nat_lit 0) A10K2.u8175 from rfl, allE_node, arows8174, irow8176, arows8175]
  all_goals rfl

theorem atot8176 : totK PA10K2 A10K2.u8176 = [0, 0, 0, 0, 1299258002364, 5799660772021, 8282856443184, 3648291799434, 397430346040, 6318667960] := by
  rw [show A10K2.u8176 = KTree.node A10K2.u8174 (nat_lit 134192310) (nat_lit 16533336620) (nat_lit 0) A10K2.u8175 from rfl, totK_node, atot8174, atot8175]
  decide +kernel

theorem arows8179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8179 = true := by
  rw [show A10K2.u8179 = KTree.node A10K2.u8177 (nat_lit 134213128) (nat_lit 14301376185) (nat_lit 0) A10K2.u8178 from rfl, allE_node, arows8177, irow8179, arows8178]
  all_goals rfl

theorem atot8179 : totK PA10K2 A10K2.u8179 = [0, 0, 0, 0, 878740748981, 4527025274007, 7729957067991, 5163364894829, 1155909907874, 67457817768] := by
  rw [show A10K2.u8179 = KTree.node A10K2.u8177 (nat_lit 134213128) (nat_lit 14301376185) (nat_lit 0) A10K2.u8178 from rfl, totK_node, atot8177, atot8178]
  decide +kernel

theorem arows6 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6 = true := by
  rw [show A10K2.u6 = KTree.node A10K2.u2 (nat_lit 18085) (nat_lit 7026826106) (nat_lit 0) A10K2.u5 from rfl, allE_node, arows2, irow6, arows5]
  all_goals rfl

theorem atot6 : totK PA10K2 A10K2.u6 = [2380035396479, 10762847940390, 15982218668684, 8316855355062, 1293364494495, 44039504522, 0, 0, 0, 0] := by
  rw [show A10K2.u6 = KTree.node A10K2.u2 (nat_lit 18085) (nat_lit 7026826106) (nat_lit 0) A10K2.u5 from rfl, totK_node, atot2, atot5]
  decide +kernel

theorem arows13 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u13 = true := by
  rw [show A10K2.u13 = KTree.node A10K2.u9 (nat_lit 49207) (nat_lit 13697746115) (nat_lit 0) A10K2.u12 from rfl, allE_node, arows9, irow13, arows12]
  all_goals rfl

theorem atot13 : totK PA10K2 A10K2.u13 = [115575618874, 2928434097133, 11738418126138, 15809635134022, 6911558695520, 942382059478, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u13 = KTree.node A10K2.u9 (nat_lit 49207) (nat_lit 13697746115) (nat_lit 0) A10K2.u12 from rfl, totK_node, atot9, atot12]
  decide +kernel

theorem arows21 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u21 = true := by
  rw [show A10K2.u21 = KTree.node A10K2.u17 (nat_lit 145118) (nat_lit 9464012413) (nat_lit 0) A10K2.u20 from rfl, allE_node, arows17, irow21, arows20]
  all_goals rfl

theorem atot21 : totK PA10K2 A10K2.u21 = [1884983728046, 9428509540965, 15399417389116, 9155741285937, 1770564318262, 94588178408, 0, 0, 0, 0] := by
  rw [show A10K2.u21 = KTree.node A10K2.u17 (nat_lit 145118) (nat_lit 9464012413) (nat_lit 0) A10K2.u20 from rfl, totK_node, atot17, atot20]
  decide +kernel

theorem arows28 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u28 = true := by
  rw [show A10K2.u28 = KTree.node A10K2.u24 (nat_lit 186529) (nat_lit 8146673625) (nat_lit 0) A10K2.u27 from rfl, allE_node, arows24, irow28, arows27]
  all_goals rfl

theorem atot28 : totK PA10K2 A10K2.u28 = [1292095572706, 6789058580544, 13799394726510, 12149995528845, 3812791598001, 392472383969, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u28 = KTree.node A10K2.u24 (nat_lit 186529) (nat_lit 8146673625) (nat_lit 0) A10K2.u27 from rfl, totK_node, atot24, atot27]
  decide +kernel

theorem arows37 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u37 = true := by
  rw [show A10K2.u37 = KTree.node A10K2.u33 (nat_lit 228818) (nat_lit 14927403618) (nat_lit 0) A10K2.u36 from rfl, allE_node, arows33, irow37, arows36]
  all_goals rfl

theorem atot37 : totK PA10K2 A10K2.u37 = [836280282984, 6023198270289, 14343505764640, 13613602823168, 4693414187782, 472179530808, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u37 = KTree.node A10K2.u33 (nat_lit 228818) (nat_lit 14927403618) (nat_lit 0) A10K2.u36 from rfl, totK_node, atot33, atot36]
  decide +kernel

theorem arows44 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u44 = true := by
  rw [show A10K2.u44 = KTree.node A10K2.u40 (nat_lit 262070) (nat_lit 17080749001) (nat_lit 0) A10K2.u43 from rfl, allE_node, arows40, irow44, arows43]
  all_goals rfl

theorem atot44 : totK PA10K2 A10K2.u44 = [0, 2147909139565, 9862939649931, 15636512895067, 9510271955513, 1895305045437, 98988825444, 0, 0, 0] := by
  rw [show A10K2.u44 = KTree.node A10K2.u40 (nat_lit 262070) (nat_lit 17080749001) (nat_lit 0) A10K2.u43 from rfl, totK_node, atot40, atot43]
  decide +kernel

theorem arows52 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u52 = true := by
  rw [show A10K2.u52 = KTree.node A10K2.u48 (nat_lit 292307) (nat_lit 8604640038) (nat_lit 0) A10K2.u51 from rfl, allE_node, arows48, irow52, arows51]
  all_goals rfl

theorem atot52 : totK PA10K2 A10K2.u52 = [0, 1063445225170, 6739936315176, 14120913877359, 11710019033303, 4044951500464, 616395076921, 30605747850, 0, 0] := by
  rw [show A10K2.u52 = KTree.node A10K2.u48 (nat_lit 292307) (nat_lit 8604640038) (nat_lit 0) A10K2.u51 from rfl, totK_node, atot48, atot51]
  decide +kernel

theorem arows59 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u59 = true := by
  rw [show A10K2.u59 = KTree.node A10K2.u55 (nat_lit 395320) (nat_lit 14437886109) (nat_lit 0) A10K2.u58 from rfl, allE_node, arows55, irow59, arows58]
  all_goals rfl

theorem atot59 : totK PA10K2 A10K2.u59 = [0, 1412337081527, 7272040940191, 14043627282697, 11475382101978, 3306127659532, 308509062959, 5528811039, 0, 0] := by
  rw [show A10K2.u59 = KTree.node A10K2.u55 (nat_lit 395320) (nat_lit 14437886109) (nat_lit 0) A10K2.u58 from rfl, totK_node, atot55, atot58]
  decide +kernel

theorem arows69 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u69 = true := by
  rw [show A10K2.u69 = KTree.node A10K2.u65 (nat_lit 429686) (nat_lit 14393282793) (nat_lit 0) A10K2.u68 from rfl, allE_node, arows65, irow69, arows68]
  all_goals rfl

theorem atot69 : totK PA10K2 A10K2.u69 = [0, 1096791628550, 6783846758124, 14231056226705, 11595703310782, 3155041223021, 274073213902, 5676195732, 0, 0] := by
  rw [show A10K2.u69 = KTree.node A10K2.u65 (nat_lit 429686) (nat_lit 14393282793) (nat_lit 0) A10K2.u68 from rfl, totK_node, atot65, atot68]
  decide +kernel

theorem arows76 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u76 = true := by
  rw [show A10K2.u76 = KTree.node A10K2.u72 (nat_lit 483905) (nat_lit 10272296125) (nat_lit 0) A10K2.u75 from rfl, allE_node, arows72, irow76, arows75]
  all_goals rfl

theorem atot76 : totK PA10K2 A10K2.u76 = [583967476257, 3624131577765, 10160886260703, 14647222928326, 8892498020718, 1813672747204, 94833092068, 0, 0, 0] := by
  rw [show A10K2.u76 = KTree.node A10K2.u72 (nat_lit 483905) (nat_lit 10272296125) (nat_lit 0) A10K2.u75 from rfl, totK_node, atot72, atot75]
  decide +kernel

theorem arows84 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u84 = true := by
  rw [show A10K2.u84 = KTree.node A10K2.u80 (nat_lit 1070266) (nat_lit 8458956418) (nat_lit 0) A10K2.u83 from rfl, allE_node, arows80, irow84, arows83]
  all_goals rfl

theorem atot84 : totK PA10K2 A10K2.u84 = [1607506249413, 8748892959925, 15844730335409, 10329577187477, 2135056554613, 118022742600, 0, 0, 0, 0] := by
  rw [show A10K2.u84 = KTree.node A10K2.u80 (nat_lit 1070266) (nat_lit 8458956418) (nat_lit 0) A10K2.u83 from rfl, totK_node, atot80, atot83]
  decide +kernel

theorem arows91 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u91 = true := by
  rw [show A10K2.u91 = KTree.node A10K2.u87 (nat_lit 1103134) (nat_lit 7224760144) (nat_lit 0) A10K2.u90 from rfl, allE_node, arows87, irow91, arows90]
  all_goals rfl

theorem atot91 : totK PA10K2 A10K2.u91 = [664492635903, 4359987834417, 11877924593407, 14294417631600, 6220327908926, 887585844657, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u91 = KTree.node A10K2.u87 (nat_lit 1103134) (nat_lit 7224760144) (nat_lit 0) A10K2.u90 from rfl, totK_node, atot87, atot90]
  decide +kernel

theorem arows100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u100 = true := by
  rw [show A10K2.u100 = KTree.node A10K2.u96 (nat_lit 1160933) (nat_lit 6531099145) (nat_lit 0) A10K2.u99 from rfl, allE_node, arows96, irow100, arows99]
  all_goals rfl

theorem atot100 : totK PA10K2 A10K2.u100 = [1218388957653, 6337006464773, 12584568763185, 11801894241704, 4980410306850, 788497175553, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u100 = KTree.node A10K2.u96 (nat_lit 1160933) (nat_lit 6531099145) (nat_lit 0) A10K2.u99 from rfl, totK_node, atot96, atot99]
  decide +kernel

theorem arows107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u107 = true := by
  rw [show A10K2.u107 = KTree.node A10K2.u103 (nat_lit 1194530) (nat_lit 8845759113) (nat_lit 0) A10K2.u106 from rfl, allE_node, arows103, irow107, arows106]
  all_goals rfl

theorem atot107 : totK PA10K2 A10K2.u107 = [1592201824328, 8855091058653, 15694795023095, 9666478696399, 1856870664024, 94588178408, 0, 0, 0, 0] := by
  rw [show A10K2.u107 = KTree.node A10K2.u103 (nat_lit 1194530) (nat_lit 8845759113) (nat_lit 0) A10K2.u106 from rfl, totK_node, atot103, atot106]
  decide +kernel

theorem arows115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u115 = true := by
  rw [show A10K2.u115 = KTree.node A10K2.u111 (nat_lit 1234984) (nat_lit 12467290254) (nat_lit 0) A10K2.u114 from rfl, allE_node, arows111, irow115, arows114]
  all_goals rfl

theorem atot115 : totK PA10K2 A10K2.u115 = [0, 2715705702575, 11628222477723, 15666853917590, 6848183980035, 968552115758, 37172849495, 0, 0, 0] := by
  rw [show A10K2.u115 = KTree.node A10K2.u111 (nat_lit 1234984) (nat_lit 12467290254) (nat_lit 0) A10K2.u114 from rfl, totK_node, atot111, atot114]
  decide +kernel

theorem arows122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u122 = true := by
  rw [show A10K2.u122 = KTree.node A10K2.u118 (nat_lit 1342515) (nat_lit 6509666921) (nat_lit 0) A10K2.u121 from rfl, allE_node, arows118, irow122, arows121]
  all_goals rfl

theorem atot122 : totK PA10K2 A10K2.u122 = [0, 2360717038405, 10743121034605, 15871512796444, 8169954797095, 1267783978170, 44660404486, 0, 0, 0] := by
  rw [show A10K2.u122 = KTree.node A10K2.u118 (nat_lit 1342515) (nat_lit 6509666921) (nat_lit 0) A10K2.u121 from rfl, totK_node, atot118, atot121]
  decide +kernel

theorem arows133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u133 = true := by
  rw [show A10K2.u133 = KTree.node A10K2.u129 (nat_lit 1451372) (nat_lit 12591573212) (nat_lit 0) A10K2.u132 from rfl, allE_node, arows129, irow133, arows132]
  all_goals rfl

theorem atot133 : totK PA10K2 A10K2.u133 = [0, 2170572464854, 10111880384365, 15541059817318, 8266000022107, 1354416835653, 67432810860, 0, 0, 0] := by
  rw [show A10K2.u133 = KTree.node A10K2.u129 (nat_lit 1451372) (nat_lit 12591573212) (nat_lit 0) A10K2.u132 from rfl, totK_node, atot129, atot132]
  decide +kernel

theorem arows140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u140 = true := by
  rw [show A10K2.u140 = KTree.node A10K2.u136 (nat_lit 1492233) (nat_lit 9152084005) (nat_lit 0) A10K2.u139 from rfl, allE_node, arows136, irow140, arows139]
  all_goals rfl

theorem atot140 : totK PA10K2 A10K2.u140 = [844183794776, 3386164465852, 6762426104266, 11505779000237, 10875558788837, 3501533373491, 384962563863, 6354482628, 0, 0] := by
  rw [show A10K2.u140 = KTree.node A10K2.u136 (nat_lit 1492233) (nat_lit 9152084005) (nat_lit 0) A10K2.u139 from rfl, totK_node, atot136, atot139]
  decide +kernel

theorem arows148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u148 = true := by
  rw [show A10K2.u148 = KTree.node A10K2.u144 (nat_lit 1599422) (nat_lit 16179429963) (nat_lit 0) A10K2.u147 from rfl, allE_node, arows144, irow148, arows147]
  all_goals rfl

theorem atot148 : totK PA10K2 A10K2.u148 = [1369210211955, 7763414429616, 15413580336178, 11770010713022, 2824292993527, 160381790870, 0, 0, 0, 0] := by
  rw [show A10K2.u148 = KTree.node A10K2.u144 (nat_lit 1599422) (nat_lit 16179429963) (nat_lit 0) A10K2.u147 from rfl, totK_node, atot144, atot147]
  decide +kernel

theorem arows155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u155 = true := by
  rw [show A10K2.u155 = KTree.node A10K2.u151 (nat_lit 1631928) (nat_lit 9786297560) (nat_lit 0) A10K2.u154 from rfl, allE_node, arows151, irow155, arows154]
  all_goals rfl

theorem atot155 : totK PA10K2 A10K2.u155 = [1267590511789, 6345182886364, 12783634040229, 12670612835761, 5484821940119, 842398789092, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u155 = KTree.node A10K2.u151 (nat_lit 1631928) (nat_lit 9786297560) (nat_lit 0) A10K2.u154 from rfl, totK_node, atot151, atot154]
  decide +kernel

theorem arows164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u164 = true := by
  rw [show A10K2.u164 = KTree.node A10K2.u160 (nat_lit 1686918) (nat_lit 15641511706) (nat_lit 0) A10K2.u163 from rfl, allE_node, arows160, irow164, arows163]
  all_goals rfl

theorem atot164 : totK PA10K2 A10K2.u164 = [903085588502, 6164450783246, 14279235836643, 13477331020142, 4816147839512, 591906260699, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u164 = KTree.node A10K2.u160 (nat_lit 1686918) (nat_lit 15641511706) (nat_lit 0) A10K2.u163 from rfl, totK_node, atot160, atot163]
  decide +kernel

theorem arows171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u171 = true := by
  rw [show A10K2.u171 = KTree.node A10K2.u167 (nat_lit 1797239) (nat_lit 14652227679) (nat_lit 0) A10K2.u170 from rfl, allE_node, arows167, irow171, arows170]
  all_goals rfl

theorem atot171 : totK PA10K2 A10K2.u171 = [1501806732195, 8187191126131, 15585655128042, 11619432762318, 2836372779778, 169749661692, 0, 0, 0, 0] := by
  rw [show A10K2.u171 = KTree.node A10K2.u167 (nat_lit 1797239) (nat_lit 14652227679) (nat_lit 0) A10K2.u170 from rfl, totK_node, atot167, atot170]
  decide +kernel

theorem arows179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u179 = true := by
  rw [show A10K2.u179 = KTree.node A10K2.u175 (nat_lit 1828538) (nat_lit 14914518105) (nat_lit 0) A10K2.u178 from rfl, allE_node, arows175, irow179, arows178]
  all_goals rfl

theorem atot179 : totK PA10K2 A10K2.u179 = [0, 2343738497890, 10524775926004, 15881251831240, 8985263441587, 1643992452533, 75062079822, 0, 0, 0] := by
  rw [show A10K2.u179 = KTree.node A10K2.u175 (nat_lit 1828538) (nat_lit 14914518105) (nat_lit 0) A10K2.u178 from rfl, totK_node, atot175, atot178]
  decide +kernel

theorem arows186 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u186 = true := by
  rw [show A10K2.u186 = KTree.node A10K2.u182 (nat_lit 1860214) (nat_lit 15283806720) (nat_lit 0) A10K2.u185 from rfl, allE_node, arows182, irow186, arows185]
  all_goals rfl

theorem atot186 : totK PA10K2 A10K2.u186 = [0, 1369210211955, 8091954956980, 15821876833662, 11200952743653, 2416243772203, 129949974888, 0, 0, 0] := by
  rw [show A10K2.u186 = KTree.node A10K2.u182 (nat_lit 1860214) (nat_lit 15283806720) (nat_lit 0) A10K2.u185 from rfl, totK_node, atot182, atot185]
  decide +kernel

theorem arows196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u196 = true := by
  rw [show A10K2.u196 = KTree.node A10K2.u192 (nat_lit 1896179) (nat_lit 8674703726) (nat_lit 0) A10K2.u195 from rfl, allE_node, arows192, irow196, arows195]
  all_goals rfl

theorem atot196 : totK PA10K2 A10K2.u196 = [0, 1386739416170, 7377303404814, 14590675428358, 12332337684396, 3910762236181, 403192215812, 7007974415, 0, 0] := by
  rw [show A10K2.u196 = KTree.node A10K2.u192 (nat_lit 1896179) (nat_lit 8674703726) (nat_lit 0) A10K2.u195 from rfl, totK_node, atot192, atot195]
  decide +kernel

theorem arows203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u203 = true := by
  rw [show A10K2.u203 = KTree.node A10K2.u199 (nat_lit 1959350) (nat_lit 16852523362) (nat_lit 0) A10K2.u202 from rfl, allE_node, arows199, irow203, arows202]
  all_goals rfl

theorem atot203 : totK PA10K2 A10K2.u203 = [0, 1036882262728, 6275376280746, 14137985764834, 13515615758452, 4663923457014, 462039179229, 7151180950, 0, 0] := by
  rw [show A10K2.u203 = KTree.node A10K2.u199 (nat_lit 1959350) (nat_lit 16852523362) (nat_lit 0) A10K2.u202 from rfl, totK_node, atot199, atot202]
  decide +kernel

theorem arows211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u211 = true := by
  rw [show A10K2.u211 = KTree.node A10K2.u207 (nat_lit 2060695) (nat_lit 14468869975) (nat_lit 0) A10K2.u210 from rfl, allE_node, arows207, irow211, arows210]
  all_goals rfl

theorem atot211 : totK PA10K2 A10K2.u211 = [0, 1245373267684, 7244600178063, 14649616682703, 12350527585054, 3902362452637, 359696652400, 6318667960, 0, 0] := by
  rw [show A10K2.u211 = KTree.node A10K2.u207 (nat_lit 2060695) (nat_lit 14468869975) (nat_lit 0) A10K2.u210 from rfl, totK_node, atot207, atot210]
  decide +kernel

theorem arows218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u218 = true := by
  rw [show A10K2.u218 = KTree.node A10K2.u214 (nat_lit 2093326) (nat_lit 10350018005) (nat_lit 0) A10K2.u217 from rfl, allE_node, arows214, irow218, arows217]
  all_goals rfl

theorem atot218 : totK PA10K2 A10K2.u218 = [0, 873069160064, 5041509834232, 11722049290816, 13308729845316, 7011106706980, 1298046544518, 67457817768, 0, 0] := by
  rw [show A10K2.u218 = KTree.node A10K2.u214 (nat_lit 2093326) (nat_lit 10350018005) (nat_lit 0) A10K2.u217 from rfl, totK_node, atot214, atot217]
  decide +kernel

theorem arows227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u227 = true := by
  rw [show A10K2.u227 = KTree.node A10K2.u223 (nat_lit 2123418) (nat_lit 11587396171) (nat_lit 0) A10K2.u226 from rfl, allE_node, arows223, irow227, arows226]
  all_goals rfl

theorem atot227 : totK PA10K2 A10K2.u227 = [0, 1503165866567, 8303222076738, 15613650583910, 10938130011990, 2258007342980, 97231139217, 0, 0, 0] := by
  rw [show A10K2.u227 = KTree.node A10K2.u223 (nat_lit 2123418) (nat_lit 11587396171) (nat_lit 0) A10K2.u226 from rfl, totK_node, atot223, atot226]
  decide +kernel

theorem arows234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u234 = true := by
  rw [show A10K2.u234 = KTree.node A10K2.u230 (nat_lit 2154889) (nat_lit 9557638051) (nat_lit 0) A10K2.u233 from rfl, allE_node, arows230, irow234, arows233]
  all_goals rfl

theorem atot234 : totK PA10K2 A10K2.u234 = [0, 800376258443, 4998563680599, 12285857979833, 13469565227476, 5710255042798, 860524571509, 36196801203, 0, 0] := by
  rw [show A10K2.u234 = KTree.node A10K2.u230 (nat_lit 2154889) (nat_lit 9557638051) (nat_lit 0) A10K2.u233 from rfl, totK_node, atot230, atot233]
  decide +kernel

theorem arows242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u242 = true := by
  rw [show A10K2.u242 = KTree.node A10K2.u238 (nat_lit 2250821) (nat_lit 6202701764) (nat_lit 0) A10K2.u241 from rfl, allE_node, arows238, irow242, arows241]
  all_goals rfl

theorem atot242 : totK PA10K2 A10K2.u242 = [0, 1198319728372, 7630904157249, 15273016762048, 10854549760312, 2212516409506, 99151423654, 0, 0, 0] := by
  rw [show A10K2.u242 = KTree.node A10K2.u238 (nat_lit 2250821) (nat_lit 6202701764) (nat_lit 0) A10K2.u241 from rfl, totK_node, atot238, atot241]
  decide +kernel

theorem arows249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u249 = true := by
  rw [show A10K2.u249 = KTree.node A10K2.u245 (nat_lit 2300965) (nat_lit 5723161990) (nat_lit 0) A10K2.u248 from rfl, allE_node, arows245, irow249, arows248]
  all_goals rfl

theorem atot249 : totK PA10K2 A10K2.u249 = [0, 2127414435650, 9499522650250, 15091095759005, 9918029853629, 2492389999658, 231726354142, 5976421810, 0, 0] := by
  rw [show A10K2.u249 = KTree.node A10K2.u245 (nat_lit 2300965) (nat_lit 5723161990) (nat_lit 0) A10K2.u248 from rfl, totK_node, atot245, atot248]
  decide +kernel

theorem arows261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u261 = true := by
  rw [show A10K2.u261 = KTree.node A10K2.u257 (nat_lit 2334192) (nat_lit 13845910136) (nat_lit 0) A10K2.u260 from rfl, allE_node, arows257, irow261, arows260]
  all_goals rfl

theorem atot261 : totK PA10K2 A10K2.u261 = [0, 0, 2671611694062, 11664633667763, 16329400338376, 7854198206354, 1123440180092, 30398153333, 0, 0] := by
  rw [show A10K2.u261 = KTree.node A10K2.u257 (nat_lit 2334192) (nat_lit 13845910136) (nat_lit 0) A10K2.u260 from rfl, totK_node, atot257, atot260]
  decide +kernel

theorem arows268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u268 = true := by
  rw [show A10K2.u268 = KTree.node A10K2.u264 (nat_lit 2377509) (nat_lit 7381318460) (nat_lit 0) A10K2.u267 from rfl, allE_node, arows264, irow268, arows267]
  all_goals rfl

theorem atot268 : totK PA10K2 A10K2.u268 = [0, 0, 2359128396243, 10836258346659, 16022094226388, 7854101623378, 1167867969429, 54467365116, 0, 0] := by
  rw [show A10K2.u268 = KTree.node A10K2.u264 (nat_lit 2377509) (nat_lit 7381318460) (nat_lit 0) A10K2.u267 from rfl, totK_node, atot264, atot267]
  decide +kernel

theorem arows276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u276 = true := by
  rw [show A10K2.u276 = KTree.node A10K2.u272 (nat_lit 2409733) (nat_lit 7008081117) (nat_lit 0) A10K2.u275 from rfl, allE_node, arows272, irow276, arows275]
  all_goals rfl

theorem atot276 : totK PA10K2 A10K2.u276 = [0, 0, 579843672931, 4402041112358, 12036418165828, 13670981186219, 5804423022706, 867178684513, 36134558889, 0] := by
  rw [show A10K2.u276 = KTree.node A10K2.u272 (nat_lit 2409733) (nat_lit 7008081117) (nat_lit 0) A10K2.u275 from rfl, totK_node, atot272, atot275]
  decide +kernel

theorem arows283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u283 = true := by
  rw [show A10K2.u283 = KTree.node A10K2.u279 (nat_lit 2508065) (nat_lit 8929195742) (nat_lit 0) A10K2.u282 from rfl, allE_node, arows279, irow283, arows282]
  all_goals rfl

theorem atot283 : totK PA10K2 A10K2.u283 = [0, 0, 1411231647218, 8332276737743, 15755432172699, 9830741850998, 1744709267410, 81393686913, 0, 0] := by
  rw [show A10K2.u283 = KTree.node A10K2.u279 (nat_lit 2508065) (nat_lit 8929195742) (nat_lit 0) A10K2.u282 from rfl, totK_node, atot279, atot282]
  decide +kernel

theorem arows292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u292 = true := by
  rw [show A10K2.u292 = KTree.node A10K2.u288 (nat_lit 2559702) (nat_lit 15156012010) (nat_lit 0) A10K2.u291 from rfl, allE_node, arows288, irow292, arows291]
  all_goals rfl

theorem atot292 : totK PA10K2 A10K2.u292 = [0, 0, 2118831955880, 9414704482353, 14807215875703, 9552100858967, 2387494601075, 248347470951, 5676195732, 0] := by
  rw [show A10K2.u292 = KTree.node A10K2.u288 (nat_lit 2559702) (nat_lit 15156012010) (nat_lit 0) A10K2.u291 from rfl, totK_node, atot288, atot291]
  decide +kernel

theorem arows299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u299 = true := by
  rw [show A10K2.u299 = KTree.node A10K2.u295 (nat_lit 3153309) (nat_lit 11933677) (nat_lit 0) A10K2.u298 from rfl, allE_node, arows295, irow299, arows298]
  all_goals rfl

theorem atot299 : totK PA10K2 A10K2.u299 = [0, 2190250867092, 9697221115960, 14481286918682, 8788243371636, 3008581199826, 598648660870, 35503361870, 0, 0] := by
  rw [show A10K2.u299 = KTree.node A10K2.u295 (nat_lit 3153309) (nat_lit 11933677) (nat_lit 0) A10K2.u298 from rfl, totK_node, atot295, atot298]
  decide +kernel

theorem arows307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u307 = true := by
  rw [show A10K2.u307 = KTree.node A10K2.u303 (nat_lit 3186162) (nat_lit 10736565383) (nat_lit 0) A10K2.u306 from rfl, allE_node, arows303, irow307, arows306]
  all_goals rfl

theorem atot307 : totK PA10K2 A10K2.u307 = [0, 293929698888, 3554460777830, 12053912743408, 15284479796948, 6461370792928, 897107722830, 36196801203, 0, 0] := by
  rw [show A10K2.u307 = KTree.node A10K2.u303 (nat_lit 3186162) (nat_lit 10736565383) (nat_lit 0) A10K2.u306 from rfl, totK_node, atot303, atot306]
  decide +kernel

theorem arows314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u314 = true := by
  rw [show A10K2.u314 = KTree.node A10K2.u310 (nat_lit 3234028) (nat_lit 11988709622) (nat_lit 0) A10K2.u313 from rfl, allE_node, arows310, irow314, arows313]
  all_goals rfl

theorem atot314 : totK PA10K2 A10K2.u314 = [0, 1182107234542, 6818663465066, 14183689826322, 11841933641381, 3439162675885, 314088020673, 6121173289, 0, 0] := by
  rw [show A10K2.u314 = KTree.node A10K2.u310 (nat_lit 3234028) (nat_lit 11988709622) (nat_lit 0) A10K2.u313 from rfl, totK_node, atot310, atot313]
  decide +kernel

theorem arows324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u324 = true := by
  rw [show A10K2.u324 = KTree.node A10K2.u320 (nat_lit 3290358) (nat_lit 12188938050) (nat_lit 0) A10K2.u323 from rfl, allE_node, arows320, irow324, arows323]
  all_goals rfl

theorem atot324 : totK PA10K2 A10K2.u324 = [0, 1996035672226, 9862968097501, 15675945713852, 8658357063951, 1469329128377, 68519843174, 0, 0, 0] := by
  rw [show A10K2.u324 = KTree.node A10K2.u320 (nat_lit 3290358) (nat_lit 12188938050) (nat_lit 0) A10K2.u323 from rfl, totK_node, atot320, atot323]
  decide +kernel

theorem arows331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u331 = true := by
  rw [show A10K2.u331 = KTree.node A10K2.u327 (nat_lit 3328699) (nat_lit 5343871908) (nat_lit 0) A10K2.u330 from rfl, allE_node, arows327, irow331, arows330]
  all_goals rfl

theorem atot331 : totK PA10K2 A10K2.u331 = [0, 0, 2789333570732, 11828196605427, 15564232672906, 6481121994325, 943207829911, 37172849495, 0, 0] := by
  rw [show A10K2.u331 = KTree.node A10K2.u327 (nat_lit 3328699) (nat_lit 5343871908) (nat_lit 0) A10K2.u330 from rfl, totK_node, atot327, atot330]
  decide +kernel

theorem arows339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u339 = true := by
  rw [show A10K2.u339 = KTree.node A10K2.u335 (nat_lit 3436589) (nat_lit 5474613880) (nat_lit 0) A10K2.u338 from rfl, allE_node, arows335, irow339, arows338]
  all_goals rfl

theorem atot339 : totK PA10K2 A10K2.u339 = [0, 0, 2644645103395, 11788545302120, 16220096972874, 6835148290144, 747819754477, 13207830636, 0, 0] := by
  rw [show A10K2.u339 = KTree.node A10K2.u335 (nat_lit 3436589) (nat_lit 5474613880) (nat_lit 0) A10K2.u338 from rfl, totK_node, atot335, atot338]
  decide +kernel

theorem arows346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u346 = true := by
  rw [show A10K2.u346 = KTree.node A10K2.u342 (nat_lit 3549864) (nat_lit 8159108071) (nat_lit 0) A10K2.u345 from rfl, allE_node, arows342, irow346, arows345]
  all_goals rfl

theorem atot346 : totK PA10K2 A10K2.u346 = [0, 0, 2164993043619, 10216639166455, 15698939919475, 7953090613053, 1219237054832, 48818064363, 0, 0] := by
  rw [show A10K2.u346 = KTree.node A10K2.u342 (nat_lit 3549864) (nat_lit 8159108071) (nat_lit 0) A10K2.u345 from rfl, totK_node, atot342, atot345]
  decide +kernel

theorem arows355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u355 = true := by
  rw [show A10K2.u355 = KTree.node A10K2.u351 (nat_lit 3594410) (nat_lit 12666844494) (nat_lit 0) A10K2.u354 from rfl, allE_node, arows351, irow355, arows354]
  all_goals rfl

theorem atot355 : totK PA10K2 A10K2.u355 = [0, 1132878220426, 4890926435051, 9013151088309, 11086658560719, 8461019704612, 2578149207377, 261362977913, 5976421810, 0] := by
  rw [show A10K2.u355 = KTree.node A10K2.u351 (nat_lit 3594410) (nat_lit 12666844494) (nat_lit 0) A10K2.u354 from rfl, totK_node, atot351, atot354]
  decide +kernel

theorem arows362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u362 = true := by
  rw [show A10K2.u362 = KTree.node A10K2.u358 (nat_lit 3701831) (nat_lit 11210411356) (nat_lit 0) A10K2.u361 from rfl, allE_node, arows358, irow362, arows361]
  all_goals rfl

theorem atot362 : totK PA10K2 A10K2.u362 = [0, 1076691216300, 6519407434402, 13876334643426, 12379509446682, 4482385058562, 657717114790, 30650496230, 0, 0] := by
  rw [show A10K2.u362 = KTree.node A10K2.u358 (nat_lit 3701831) (nat_lit 11210411356) (nat_lit 0) A10K2.u361 from rfl, totK_node, atot358, atot361]
  decide +kernel

theorem arows370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u370 = true := by
  rw [show A10K2.u370 = KTree.node A10K2.u366 (nat_lit 3749719) (nat_lit 5476407970) (nat_lit 0) A10K2.u369 from rfl, allE_node, arows366, irow370, arows369]
  all_goals rfl

theorem atot370 : totK PA10K2 A10K2.u370 = [0, 1387949460702, 7866670153970, 15634283336751, 12272108438434, 3148188136014, 203084350986, 0, 0, 0] := by
  rw [show A10K2.u370 = KTree.node A10K2.u366 (nat_lit 3749719) (nat_lit 5476407970) (nat_lit 0) A10K2.u369 from rfl, totK_node, atot366, atot369]
  decide +kernel

theorem arows377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u377 = true := by
  rw [show A10K2.u377 = KTree.node A10K2.u373 (nat_lit 3869452) (nat_lit 11666030505) (nat_lit 0) A10K2.u376 from rfl, allE_node, arows373, irow377, arows376]
  all_goals rfl

theorem atot377 : totK PA10K2 A10K2.u377 = [0, 1409167831787, 7549822910980, 14650476781041, 12097143055876, 3957389881616, 401938395119, 7380853412, 0, 0] := by
  rw [show A10K2.u377 = KTree.node A10K2.u373 (nat_lit 3869452) (nat_lit 11666030505) (nat_lit 0) A10K2.u376 from rfl, totK_node, atot373, atot376]
  decide +kernel

theorem arows388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u388 = true := by
  rw [show A10K2.u388 = KTree.node A10K2.u384 (nat_lit 3899890) (nat_lit 12106734119) (nat_lit 0) A10K2.u387 from rfl, allE_node, arows384, irow388, arows387]
  all_goals rfl

theorem atot388 : totK PA10K2 A10K2.u388 = [0, 873621053165, 5606870054253, 13345466080104, 13757074762994, 5467794177543, 635331538242, 13671283666, 0, 0] := by
  rw [show A10K2.u388 = KTree.node A10K2.u384 (nat_lit 3899890) (nat_lit 12106734119) (nat_lit 0) A10K2.u387 from rfl, totK_node, atot384, atot387]
  decide +kernel

theorem arows395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u395 = true := by
  rw [show A10K2.u395 = KTree.node A10K2.u391 (nat_lit 8388868) (nat_lit 12865384108) (nat_lit 0) A10K2.u394 from rfl, allE_node, arows391, irow395, arows394]
  all_goals rfl

theorem atot395 : totK PA10K2 A10K2.u395 = [1342080028200, 5654551948207, 8939395991330, 8586454897205, 8286623317236, 5080414272783, 1073448159147, 61110126106, 0, 0] := by
  rw [show A10K2.u395 = KTree.node A10K2.u391 (nat_lit 8388868) (nat_lit 12865384108) (nat_lit 0) A10K2.u394 from rfl, totK_node, atot391, atot394]
  decide +kernel

theorem arows403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u403 = true := by
  rw [show A10K2.u403 = KTree.node A10K2.u399 (nat_lit 8420864) (nat_lit 15265208472) (nat_lit 0) A10K2.u402 from rfl, allE_node, arows399, irow403, arows402]
  all_goals rfl

theorem atot403 : totK PA10K2 A10K2.u403 = [950866415105, 6214906747689, 13788367609065, 12714636638721, 4679105003181, 668267596811, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u403 = KTree.node A10K2.u399 (nat_lit 8420864) (nat_lit 15265208472) (nat_lit 0) A10K2.u402 from rfl, totK_node, atot399, atot402]
  decide +kernel

theorem arows410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u410 = true := by
  rw [show A10K2.u410 = KTree.node A10K2.u406 (nat_lit 8522020) (nat_lit 14146055856) (nat_lit 0) A10K2.u409 from rfl, allE_node, arows406, irow410, arows409]
  all_goals rfl

theorem atot410 : totK PA10K2 A10K2.u410 = [1305015298455, 7125668277381, 14203305602912, 11867310381846, 3627200677435, 331323071471, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u410 = KTree.node A10K2.u406 (nat_lit 8522020) (nat_lit 14146055856) (nat_lit 0) A10K2.u409 from rfl, totK_node, atot406, atot409]
  decide +kernel

theorem arows419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u419 = true := by
  rw [show A10K2.u419 = KTree.node A10K2.u415 (nat_lit 8555329) (nat_lit 8816870068) (nat_lit 0) A10K2.u418 from rfl, allE_node, arows415, irow419, arows418]
  all_goals rfl

theorem atot419 : totK PA10K2 A10K2.u419 = [809888342482, 5855432800416, 14051079008039, 12883107410636, 3664674057748, 258774460212, 0, 0, 0, 0] := by
  rw [show A10K2.u419 = KTree.node A10K2.u415 (nat_lit 8555329) (nat_lit 8816870068) (nat_lit 0) A10K2.u418 from rfl, totK_node, atot415, atot418]
  decide +kernel

theorem arows426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u426 = true := by
  rw [show A10K2.u426 = KTree.node A10K2.u422 (nat_lit 8612870) (nat_lit 15385015361) (nat_lit 0) A10K2.u425 from rfl, allE_node, arows422, irow426, arows425]
  all_goals rfl

theorem atot426 : totK PA10K2 A10K2.u426 = [1605739312950, 8300819859569, 15224371220043, 11480156295928, 3322771045271, 335791808118, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u426 = KTree.node A10K2.u422 (nat_lit 8612870) (nat_lit 15385015361) (nat_lit 0) A10K2.u425 from rfl, totK_node, atot422, atot425]
  decide +kernel

theorem arows434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u434 = true := by
  rw [show A10K2.u434 = KTree.node A10K2.u430 (nat_lit 8650736) (nat_lit 13305762731) (nat_lit 0) A10K2.u433 from rfl, allE_node, arows430, irow434, arows433]
  all_goals rfl

theorem atot434 : totK PA10K2 A10K2.u434 = [0, 2107842124863, 9920390878034, 15858120072088, 9519581824493, 1890857800290, 98846728256, 0, 0, 0] := by
  rw [show A10K2.u434 = KTree.node A10K2.u430 (nat_lit 8650736) (nat_lit 13305762731) (nat_lit 0) A10K2.u433 from rfl, totK_node, atot430, atot433]
  decide +kernel

theorem arows441 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u441 = true := by
  rw [show A10K2.u441 = KTree.node A10K2.u437 (nat_lit 8683013) (nat_lit 4771110605) (nat_lit 0) A10K2.u440 from rfl, allE_node, arows437, irow441, arows440]
  all_goals rfl

theorem atot441 : totK PA10K2 A10K2.u441 = [0, 977401383692, 6361765044702, 13955767786528, 12219590524314, 4330262252468, 642105666870, 30605747850, 0, 0] := by
  rw [show A10K2.u441 = KTree.node A10K2.u437 (nat_lit 8683013) (nat_lit 4771110605) (nat_lit 0) A10K2.u440 from rfl, totK_node, atot437, atot440]
  decide +kernel

theorem arows451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u451 = true := by
  rw [show A10K2.u451 = KTree.node A10K2.u447 (nat_lit 8784737) (nat_lit 8407456939) (nat_lit 0) A10K2.u450 from rfl, allE_node, arows447, irow451, arows450]
  all_goals rfl

theorem atot451 : totK PA10K2 A10K2.u451 = [0, 1581776753472, 7860810881206, 14348934306154, 11020032544200, 3028914996779, 282798473010, 5528811039, 0, 0] := by
  rw [show A10K2.u451 = KTree.node A10K2.u447 (nat_lit 8784737) (nat_lit 8407456939) (nat_lit 0) A10K2.u450 from rfl, totK_node, atot447, atot450]
  decide +kernel

theorem arows458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u458 = true := by
  rw [show A10K2.u458 = KTree.node A10K2.u454 (nat_lit 8824065) (nat_lit 7089438265) (nat_lit 0) A10K2.u457 from rfl, allE_node, arows454, irow458, arows457]
  all_goals rfl

theorem atot458 : totK PA10K2 A10K2.u458 = [0, 1042277994914, 6705028189697, 14465244400480, 11752880924017, 3147087138799, 274073213902, 5676195732, 0, 0] := by
  rw [show A10K2.u458 = KTree.node A10K2.u454 (nat_lit 8824065) (nat_lit 7089438265) (nat_lit 0) A10K2.u457 from rfl, totK_node, atot454, atot457]
  decide +kernel

theorem arows466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u466 = true := by
  rw [show A10K2.u466 = KTree.node A10K2.u462 (nat_lit 8877202) (nat_lit 15858721076) (nat_lit 0) A10K2.u465 from rfl, allE_node, arows462, irow466, arows465]
  all_goals rfl

theorem atot466 : totK PA10K2 A10K2.u466 = [843291061595, 4909799758124, 11564781005132, 13598577734927, 7394286989190, 1545808522066, 87681911118, 0, 0, 0] := by
  rw [show A10K2.u466 = KTree.node A10K2.u462 (nat_lit 8877202) (nat_lit 15858721076) (nat_lit 0) A10K2.u465 from rfl, totK_node, atot462, atot465]
  decide +kernel

theorem arows473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u473 = true := by
  rw [show A10K2.u473 = KTree.node A10K2.u469 (nat_lit 9008296) (nat_lit 3583783990) (nat_lit 0) A10K2.u472 from rfl, allE_node, arows469, irow473, arows472]
  all_goals rfl

theorem atot473 : totK PA10K2 A10K2.u473 = [1342370522690, 7197005934291, 13944986248399, 11577329685765, 4213687240964, 627738181435, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u473 = KTree.node A10K2.u469 (nat_lit 9008296) (nat_lit 3583783990) (nat_lit 0) A10K2.u472 from rfl, totK_node, atot469, atot472]
  decide +kernel

theorem arows482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u482 = true := by
  rw [show A10K2.u482 = KTree.node A10K2.u478 (nat_lit 9044064) (nat_lit 13929524539) (nat_lit 0) A10K2.u481 from rfl, allE_node, arows478, irow482, arows481]
  all_goals rfl

theorem atot482 : totK PA10K2 A10K2.u482 = [1330226076531, 7049181310535, 13784280739640, 11968504516553, 4108414038500, 397389065170, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u482 = KTree.node A10K2.u478 (nat_lit 9044064) (nat_lit 13929524539) (nat_lit 0) A10K2.u481 from rfl, totK_node, atot478, atot481]
  decide +kernel

theorem arows489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u489 = true := by
  rw [show A10K2.u489 = KTree.node A10K2.u485 (nat_lit 9077134) (nat_lit 13192143130) (nat_lit 0) A10K2.u488 from rfl, allE_node, arows485, irow489, arows488]
  all_goals rfl

theorem atot489 : totK PA10K2 A10K2.u489 = [818722742184, 6399174670734, 15105601201461, 12611105688374, 3013691378970, 166078996937, 0, 0, 0, 0] := by
  rw [show A10K2.u489 = KTree.node A10K2.u485 (nat_lit 9077134) (nat_lit 13192143130) (nat_lit 0) A10K2.u488 from rfl, totK_node, atot485, atot488]
  decide +kernel

theorem arows497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u497 = true := by
  rw [show A10K2.u497 = KTree.node A10K2.u493 (nat_lit 9256156) (nat_lit 10111373352) (nat_lit 0) A10K2.u496 from rfl, allE_node, arows493, irow497, arows496]
  all_goals rfl

theorem atot497 : totK PA10K2 A10K2.u497 = [0, 2181401843152, 10425587726491, 16107343812136, 8336546567867, 1257012843909, 44362905215, 0, 0, 0] := by
  rw [show A10K2.u497 = KTree.node A10K2.u493 (nat_lit 9256156) (nat_lit 10111373352) (nat_lit 0) A10K2.u496 from rfl, totK_node, atot493, atot496]
  decide +kernel

theorem arows504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u504 = true := by
  rw [show A10K2.u504 = KTree.node A10K2.u500 (nat_lit 9289159) (nat_lit 7623788678) (nat_lit 0) A10K2.u503 from rfl, allE_node, arows500, irow504, arows503]
  all_goals rfl

theorem atot504 : totK PA10K2 A10K2.u504 = [0, 277343490675, 3493896892674, 12037111536665, 15180666239295, 6486644085257, 912086367573, 36704093874, 0, 0] := by
  rw [show A10K2.u504 = KTree.node A10K2.u500 (nat_lit 9289159) (nat_lit 7623788678) (nat_lit 0) A10K2.u503 from rfl, totK_node, atot500, atot503]
  decide +kernel

theorem arows517 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u517 = true := by
  rw [show A10K2.u517 = KTree.node A10K2.u513 (nat_lit 9321111) (nat_lit 11036217250) (nat_lit 0) A10K2.u516 from rfl, allE_node, arows513, irow517, arows516]
  all_goals rfl

theorem atot517 : totK PA10K2 A10K2.u517 = [0, 1870875409714, 9667493557204, 16114275807523, 9001533737845, 1395061115025, 48969716871, 0, 0, 0] := by
  rw [show A10K2.u517 = KTree.node A10K2.u513 (nat_lit 9321111) (nat_lit 11036217250) (nat_lit 0) A10K2.u516 from rfl, totK_node, atot513, atot516]
  decide +kernel

theorem arows524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u524 = true := by
  rw [show A10K2.u524 = KTree.node A10K2.u520 (nat_lit 9361746) (nat_lit 13648117361) (nat_lit 0) A10K2.u523 from rfl, allE_node, arows520, irow524, arows523]
  all_goals rfl

theorem atot524 : totK PA10K2 A10K2.u524 = [1257633742337, 5132856533757, 8801478636960, 10469683463702, 9049501975695, 2880420672947, 290955089110, 6239673734, 0, 0] := by
  rw [show A10K2.u524 = KTree.node A10K2.u520 (nat_lit 9361746) (nat_lit 13648117361) (nat_lit 0) A10K2.u523 from rfl, totK_node, atot520, atot523]
  decide +kernel

theorem arows532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u532 = true := by
  rw [show A10K2.u532 = KTree.node A10K2.u528 (nat_lit 9470024) (nat_lit 13804082660) (nat_lit 0) A10K2.u531 from rfl, allE_node, arows528, irow532, arows531]
  all_goals rfl

theorem atot532 : totK PA10K2 A10K2.u532 = [836330893060, 6055479083306, 13824301575223, 12655187883697, 4642714260679, 668508228637, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u532 = KTree.node A10K2.u528 (nat_lit 9470024) (nat_lit 13804082660) (nat_lit 0) A10K2.u531 from rfl, totK_node, atot528, atot531]
  decide +kernel

theorem arows539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u539 = true := by
  rw [show A10K2.u539 = KTree.node A10K2.u535 (nat_lit 9516251) (nat_lit 9773256128) (nat_lit 0) A10K2.u538 from rfl, allE_node, arows535, irow539, arows538]
  all_goals rfl

theorem atot539 : totK PA10K2 A10K2.u539 = [1655480738539, 8037330245110, 14330819987130, 10962695447941, 3215455988964, 301189961371, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u539 = KTree.node A10K2.u535 (nat_lit 9516251) (nat_lit 9773256128) (nat_lit 0) A10K2.u538 from rfl, totK_node, atot535, atot538]
  decide +kernel

theorem arows548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u548 = true := by
  rw [show A10K2.u548 = KTree.node A10K2.u544 (nat_lit 9552385) (nat_lit 10502688798) (nat_lit 0) A10K2.u547 from rfl, allE_node, arows544, irow548, arows547]
  all_goals rfl

theorem atot548 : totK PA10K2 A10K2.u548 = [735145280061, 4901736518243, 12124288332445, 13525117686088, 6037561462430, 888387238718, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u548 = KTree.node A10K2.u544 (nat_lit 9552385) (nat_lit 10502688798) (nat_lit 0) A10K2.u547 from rfl, totK_node, atot544, atot547]
  decide +kernel

theorem arows555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u555 = true := by
  rw [show A10K2.u555 = KTree.node A10K2.u551 (nat_lit 9582881) (nat_lit 9173356087) (nat_lit 0) A10K2.u554 from rfl, allE_node, arows551, irow555, arows554]
  all_goals rfl

theorem atot555 : totK PA10K2 A10K2.u555 = [1718287320734, 8944757582986, 15524712872052, 9682506631734, 1864250312854, 94588178408, 0, 0, 0, 0] := by
  rw [show A10K2.u555 = KTree.node A10K2.u551 (nat_lit 9582881) (nat_lit 9173356087) (nat_lit 0) A10K2.u554 from rfl, totK_node, atot551, atot554]
  decide +kernel

theorem arows563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u563 = true := by
  rw [show A10K2.u563 = KTree.node A10K2.u559 (nat_lit 9621617) (nat_lit 7152264158) (nat_lit 0) A10K2.u562 from rfl, allE_node, arows559, irow563, arows562]
  all_goals rfl

theorem atot563 : totK PA10K2 A10K2.u563 = [0, 2765219779284, 11692633982340, 15632450050659, 6786912435141, 968433075059, 37172849495, 0, 0, 0] := by
  rw [show A10K2.u563 = KTree.node A10K2.u559 (nat_lit 9621617) (nat_lit 7152264158) (nat_lit 0) A10K2.u562 from rfl, totK_node, atot559, atot562]
  decide +kernel

theorem arows570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u570 = true := by
  rw [show A10K2.u570 = KTree.node A10K2.u566 (nat_lit 9728561) (nat_lit 9935575717) (nat_lit 0) A10K2.u569 from rfl, allE_node, arows566, irow570, arows569]
  all_goals rfl

theorem atot570 : totK PA10K2 A10K2.u570 = [0, 2447057686530, 10866540526956, 15770181169330, 8223514413517, 1307654977067, 44660404486, 0, 0, 0] := by
  rw [show A10K2.u570 = KTree.node A10K2.u566 (nat_lit 9728561) (nat_lit 9935575717) (nat_lit 0) A10K2.u569 from rfl, totK_node, atot566, atot569]
  decide +kernel

theorem arows580 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u580 = true := by
  rw [show A10K2.u580 = KTree.node A10K2.u576 (nat_lit 9833235) (nat_lit 10182961065) (nat_lit 0) A10K2.u579 from rfl, allE_node, arows576, irow580, arows579]
  all_goals rfl

theorem atot580 : totK PA10K2 A10K2.u580 = [0, 2009337304470, 9947074256758, 15885492626485, 8533102194801, 1385914172185, 68361337650, 0, 0, 0] := by
  rw [show A10K2.u580 = KTree.node A10K2.u576 (nat_lit 9833235) (nat_lit 10182961065) (nat_lit 0) A10K2.u579 from rfl, totK_node, atot576, atot579]
  decide +kernel

theorem arows587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u587 = true := by
  rw [show A10K2.u587 = KTree.node A10K2.u583 (nat_lit 9865426) (nat_lit 14391394561) (nat_lit 0) A10K2.u586 from rfl, allE_node, arows583, irow587, arows586]
  all_goals rfl

theorem atot587 : totK PA10K2 A10K2.u587 = [0, 846685665495, 6309587287260, 14769842367303, 12088668500186, 2900632131321, 183727060230, 0, 0, 0] := by
  rw [show A10K2.u587 = KTree.node A10K2.u583 (nat_lit 9865426) (nat_lit 14391394561) (nat_lit 0) A10K2.u586 from rfl, totK_node, atot583, atot586]
  decide +kernel

theorem arows595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u595 = true := by
  rw [show A10K2.u595 = KTree.node A10K2.u591 (nat_lit 10502662) (nat_lit 14005300912) (nat_lit 0) A10K2.u594 from rfl, allE_node, arows591, irow595, arows594]
  all_goals rfl

theorem atot595 : totK PA10K2 A10K2.u595 = [0, 2292946443305, 10266284036555, 15271789269289, 8551295083086, 1973168237986, 244455875708, 6354482628, 0, 0] := by
  rw [show A10K2.u595 = KTree.node A10K2.u591 (nat_lit 10502662) (nat_lit 14005300912) (nat_lit 0) A10K2.u594 from rfl, totK_node, atot591, atot594]
  decide +kernel

theorem arows602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u602 = true := by
  rw [show A10K2.u602 = KTree.node A10K2.u598 (nat_lit 10534926) (nat_lit 13335700714) (nat_lit 0) A10K2.u601 from rfl, allE_node, arows598, irow602, arows601]
  all_goals rfl

theorem atot602 : totK PA10K2 A10K2.u602 = [0, 304661711030, 3421843886434, 11910566110478, 15586806092384, 6607379899573, 901873974653, 36196801203, 0, 0] := by
  rw [show A10K2.u602 = KTree.node A10K2.u598 (nat_lit 10534926) (nat_lit 13335700714) (nat_lit 0) A10K2.u601 from rfl, totK_node, atot598, atot601]
  decide +kernel

theorem arows611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u611 = true := by
  rw [show A10K2.u611 = KTree.node A10K2.u607 (nat_lit 10630874) (nat_lit 13062609685) (nat_lit 0) A10K2.u610 from rfl, allE_node, arows607, irow611, arows610]
  all_goals rfl

theorem atot611 : totK PA10K2 A10K2.u611 = [0, 1810241929907, 9357395368772, 15680318866845, 9243238676487, 1697526094478, 88767123718, 0, 0, 0] := by
  rw [show A10K2.u611 = KTree.node A10K2.u607 (nat_lit 10630874) (nat_lit 13062609685) (nat_lit 0) A10K2.u610 from rfl, totK_node, atot607, atot610]
  decide +kernel

theorem arows618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u618 = true := by
  rw [show A10K2.u618 = KTree.node A10K2.u614 (nat_lit 10671318) (nat_lit 10299269237) (nat_lit 0) A10K2.u617 from rfl, allE_node, arows614, irow618, arows617]
  all_goals rfl

theorem atot618 : totK PA10K2 A10K2.u618 = [0, 1095933414401, 6442469943469, 14004003453616, 12607662261905, 3888491130563, 397423314273, 6354482628, 0, 0] := by
  rw [show A10K2.u618 = KTree.node A10K2.u614 (nat_lit 10671318) (nat_lit 10299269237) (nat_lit 0) A10K2.u617 from rfl, totK_node, atot614, atot617]
  decide +kernel

theorem arows626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u626 = true := by
  rw [show A10K2.u626 = KTree.node A10K2.u622 (nat_lit 10718650) (nat_lit 13661878078) (nat_lit 0) A10K2.u625 from rfl, allE_node, arows622, irow626, arows625]
  all_goals rfl

theorem atot626 : totK PA10K2 A10K2.u626 = [0, 1092675843394, 6542972112078, 14233461355438, 13307166809855, 4603246340327, 454801381552, 6904928264, 0, 0] := by
  rw [show A10K2.u626 = KTree.node A10K2.u622 (nat_lit 10718650) (nat_lit 13661878078) (nat_lit 0) A10K2.u625 from rfl, totK_node, atot622, atot625]
  decide +kernel

theorem arows633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u633 = true := by
  rw [show A10K2.u633 = KTree.node A10K2.u629 (nat_lit 11097491) (nat_lit 10717197745) (nat_lit 0) A10K2.u632 from rfl, allE_node, arows629, irow633, arows632]
  all_goals rfl

theorem atot633 : totK PA10K2 A10K2.u633 = [0, 1600939985814, 8641985451834, 15865394840855, 10647847487567, 2192811762765, 106682219597, 0, 0, 0] := by
  rw [show A10K2.u633 = KTree.node A10K2.u629 (nat_lit 11097491) (nat_lit 10717197745) (nat_lit 0) A10K2.u632 from rfl, totK_node, atot629, atot632]
  decide +kernel

theorem arows644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u644 = true := by
  rw [show A10K2.u644 = KTree.node A10K2.u640 (nat_lit 11130914) (nat_lit 9062839623) (nat_lit 0) A10K2.u643 from rfl, allE_node, arows640, irow644, arows643]
  all_goals rfl

theorem atot644 : totK PA10K2 A10K2.u644 = [0, 771637207475, 4603409154091, 11811934109995, 13883051007209, 6195703178764, 897581558064, 37204059898, 0, 0] := by
  rw [show A10K2.u644 = KTree.node A10K2.u640 (nat_lit 11130914) (nat_lit 9062839623) (nat_lit 0) A10K2.u643 from rfl, totK_node, atot640, atot643]
  decide +kernel

theorem arows651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u651 = true := by
  rw [show A10K2.u651 = KTree.node A10K2.u647 (nat_lit 11159778) (nat_lit 13874746428) (nat_lit 0) A10K2.u650 from rfl, allE_node, arows647, irow651, arows650]
  all_goals rfl

theorem atot651 : totK PA10K2 A10K2.u651 = [0, 1371870059023, 8247274406755, 15705969423530, 10751905299452, 2150535360612, 102152434533, 0, 0, 0] := by
  rw [show A10K2.u651 = KTree.node A10K2.u647 (nat_lit 11159778) (nat_lit 13874746428) (nat_lit 0) A10K2.u650 from rfl, totK_node, atot647, atot650]
  decide +kernel

theorem arows659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u659 = true := by
  rw [show A10K2.u659 = KTree.node A10K2.u655 (nat_lit 11537480) (nat_lit 13706594045) (nat_lit 0) A10K2.u658 from rfl, allE_node, arows655, irow659, arows658]
  all_goals rfl

theorem atot659 : totK PA10K2 A10K2.u659 = [0, 1591182940321, 7993617497217, 14196737562476, 10596889346265, 3117735485316, 353745666798, 6354482628, 0, 0] := by
  rw [show A10K2.u659 = KTree.node A10K2.u655 (nat_lit 11537480) (nat_lit 13706594045) (nat_lit 0) A10K2.u658 from rfl, totK_node, atot655, atot658]
  decide +kernel

theorem arows666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u666 = true := by
  rw [show A10K2.u666 = KTree.node A10K2.u662 (nat_lit 11571461) (nat_lit 6832680661) (nat_lit 0) A10K2.u665 from rfl, allE_node, arows662, irow666, arows665]
  all_goals rfl

theorem atot666 : totK PA10K2 A10K2.u666 = [0, 500094607715, 4394662826163, 12833690473195, 14419723058192, 5474972152683, 737920370947, 35767183343, 0, 0] := by
  rw [show A10K2.u666 = KTree.node A10K2.u662 (nat_lit 11571461) (nat_lit 6832680661) (nat_lit 0) A10K2.u665 from rfl, totK_node, atot662, atot665]
  decide +kernel

theorem arows675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u675 = true := by
  rw [show A10K2.u675 = KTree.node A10K2.u671 (nat_lit 11617633) (nat_lit 8212835464) (nat_lit 0) A10K2.u674 from rfl, allE_node, arows671, irow675, arows674]
  all_goals rfl

theorem atot675 : totK PA10K2 A10K2.u675 = [0, 1811215867801, 9204777843628, 15753422215815, 9908557573777, 1883258870259, 78347549206, 0, 0, 0] := by
  rw [show A10K2.u675 = KTree.node A10K2.u671 (nat_lit 11617633) (nat_lit 8212835464) (nat_lit 0) A10K2.u674 from rfl, totK_node, atot671, atot674]
  decide +kernel

theorem arows682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u682 = true := by
  rw [show A10K2.u682 = KTree.node A10K2.u678 (nat_lit 11655445) (nat_lit 7051909534) (nat_lit 0) A10K2.u681 from rfl, allE_node, arows678, irow682, arows681]
  all_goals rfl

theorem atot682 : totK PA10K2 A10K2.u682 = [0, 1025773855106, 5542877157849, 12261990628918, 12913959252803, 5287482801723, 760118598081, 36768997705, 0, 0] := by
  rw [show A10K2.u682 = KTree.node A10K2.u678 (nat_lit 11655445) (nat_lit 7051909534) (nat_lit 0) A10K2.u681 from rfl, totK_node, atot678, atot681]
  decide +kernel

theorem arows690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u690 = true := by
  rw [show A10K2.u690 = KTree.node A10K2.u686 (nat_lit 11684678) (nat_lit 7794162768) (nat_lit 0) A10K2.u689 from rfl, allE_node, arows686, irow690, arows689]
  all_goals rfl

theorem atot690 : totK PA10K2 A10K2.u690 = [0, 1265119596279, 7749430023823, 15409842343737, 10944714903926, 2180439446719, 108946306362, 0, 0, 0] := by
  rw [show A10K2.u690 = KTree.node A10K2.u686 (nat_lit 11684678) (nat_lit 7794162768) (nat_lit 0) A10K2.u689 from rfl, totK_node, atot686, atot689]
  decide +kernel

theorem arows697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u697 = true := by
  rw [show A10K2.u697 = KTree.node A10K2.u693 (nat_lit 11799601) (nat_lit 9866223381) (nat_lit 0) A10K2.u696 from rfl, allE_node, arows693, irow697, arows696]
  all_goals rfl

theorem atot697 : totK PA10K2 A10K2.u697 = [0, 0, 2427050981135, 11171632939621, 15949187870231, 7002076893088, 965368466251, 36743231635, 0, 0] := by
  rw [show A10K2.u697 = KTree.node A10K2.u693 (nat_lit 11799601) (nat_lit 9866223381) (nat_lit 0) A10K2.u696 from rfl, totK_node, atot693, atot696]
  decide +kernel

theorem arows707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u707 = true := by
  rw [show A10K2.u707 = KTree.node A10K2.u703 (nat_lit 11877783) (nat_lit 14535722111) (nat_lit 0) A10K2.u706 from rfl, allE_node, arows703, irow707, arows706]
  all_goals rfl

theorem atot707 : totK PA10K2 A10K2.u707 = [0, 0, 2769800667825, 11482643657991, 15631778994360, 7232397322661, 1075044976338, 43726476913, 0, 0] := by
  rw [show A10K2.u707 = KTree.node A10K2.u703 (nat_lit 11877783) (nat_lit 14535722111) (nat_lit 0) A10K2.u706 from rfl, totK_node, atot703, atot706]
  decide +kernel

theorem arows714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u714 = true := by
  rw [show A10K2.u714 = KTree.node A10K2.u710 (nat_lit 11942150) (nat_lit 4683817129) (nat_lit 0) A10K2.u713 from rfl, allE_node, arows710, irow714, arows713]
  all_goals rfl

theorem atot714 : totK PA10K2 A10K2.u714 = [0, 0, 1813448055304, 9412871440796, 15617416459425, 8521046184573, 1573697448163, 92271558297, 0, 0] := by
  rw [show A10K2.u714 = KTree.node A10K2.u710 (nat_lit 11942150) (nat_lit 4683817129) (nat_lit 0) A10K2.u713 from rfl, totK_node, atot710, atot713]
  decide +kernel

theorem arows722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u722 = true := by
  rw [show A10K2.u722 = KTree.node A10K2.u718 (nat_lit 11983013) (nat_lit 7333572875) (nat_lit 0) A10K2.u721 from rfl, allE_node, arows718, irow722, arows721]
  all_goals rfl

theorem atot722 : totK PA10K2 A10K2.u722 = [1151305832182, 4879407166609, 6995706997590, 5564488837605, 7674698984356, 7948072777339, 2925324071350, 353769333798, 6354482628, 0] := by
  rw [show A10K2.u722 = KTree.node A10K2.u718 (nat_lit 11983013) (nat_lit 7333572875) (nat_lit 0) A10K2.u721 from rfl, totK_node, atot718, atot721]
  decide +kernel

theorem arows729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u729 = true := by
  rw [show A10K2.u729 = KTree.node A10K2.u725 (nat_lit 12612849) (nat_lit 5225980963) (nat_lit 0) A10K2.u728 from rfl, allE_node, arows725, irow729, arows728]
  all_goals rfl

theorem atot729 : totK PA10K2 A10K2.u729 = [1149097285407, 6678521702420, 13802698450619, 12156976404867, 4479405881946, 640270809416, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u729 = KTree.node A10K2.u725 (nat_lit 12612849) (nat_lit 5225980963) (nat_lit 0) A10K2.u728 from rfl, totK_node, atot725, atot728]
  decide +kernel

theorem arows738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u738 = true := by
  rw [show A10K2.u738 = KTree.node A10K2.u734 (nat_lit 12714377) (nat_lit 9623824707) (nat_lit 0) A10K2.u737 from rfl, allE_node, arows734, irow738, arows737]
  all_goals rfl

theorem atot738 : totK PA10K2 A10K2.u738 = [1534855864381, 7625254922913, 14097527795002, 11617536575647, 3691769108482, 339102431098, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u738 = KTree.node A10K2.u734 (nat_lit 12714377) (nat_lit 9623824707) (nat_lit 0) A10K2.u737 from rfl, totK_node, atot734, atot737]
  decide +kernel

theorem arows745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u745 = true := by
  rw [show A10K2.u745 = KTree.node A10K2.u741 (nat_lit 12765703) (nat_lit 8645632164) (nat_lit 0) A10K2.u744 from rfl, allE_node, arows741, irow745, arows744]
  all_goals rfl

theorem atot745 : totK PA10K2 A10K2.u745 = [801349738877, 6123210495243, 14510293073491, 12806823201311, 3854595650507, 391989195675, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u745 = KTree.node A10K2.u741 (nat_lit 12765703) (nat_lit 8645632164) (nat_lit 0) A10K2.u744 from rfl, totK_node, atot741, atot744]
  decide +kernel

theorem arows753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u753 = true := by
  rw [show A10K2.u753 = KTree.node A10K2.u749 (nat_lit 12808291) (nat_lit 2263793732) (nat_lit 0) A10K2.u752 from rfl, allE_node, arows749, irow753, arows752]
  all_goals rfl

theorem atot753 : totK PA10K2 A10K2.u753 = [1420687879820, 7508546378706, 14546470876559, 12050659385401, 3847536012375, 393728174347, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u753 = KTree.node A10K2.u749 (nat_lit 12808291) (nat_lit 2263793732) (nat_lit 0) A10K2.u752 from rfl, totK_node, atot749, atot752]
  decide +kernel

theorem arows760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u760 = true := by
  rw [show A10K2.u760 = KTree.node A10K2.u756 (nat_lit 12840923) (nat_lit 5887713756) (nat_lit 0) A10K2.u759 from rfl, allE_node, arows756, irow760, arows759]
  all_goals rfl

theorem atot760 : totK PA10K2 A10K2.u760 = [0, 2278233237763, 10290648314267, 15804152916413, 9232153077604, 1749729451322, 88227914373, 0, 0, 0] := by
  rw [show A10K2.u760 = KTree.node A10K2.u756 (nat_lit 12840923) (nat_lit 5887713756) (nat_lit 0) A10K2.u759 from rfl, totK_node, atot756, atot759]
  decide +kernel

theorem arows772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u772 = true := by
  rw [show A10K2.u772 = KTree.node A10K2.u768 (nat_lit 12872759) (nat_lit 14949959527) (nat_lit 0) A10K2.u771 from rfl, allE_node, arows768, irow772, arows771]
  all_goals rfl

theorem atot772 : totK PA10K2 A10K2.u772 = [0, 1441022009178, 8087121244772, 15490997390350, 11118458505466, 2563546818354, 160009480803, 0, 0, 0] := by
  rw [show A10K2.u772 = KTree.node A10K2.u768 (nat_lit 12872759) (nat_lit 14949959527) (nat_lit 0) A10K2.u771 from rfl, totK_node, atot768, atot771]
  decide +kernel

theorem arows779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u779 = true := by
  rw [show A10K2.u779 = KTree.node A10K2.u775 (nat_lit 12905659) (nat_lit 6846431645) (nat_lit 0) A10K2.u778 from rfl, allE_node, arows775, irow779, arows778]
  all_goals rfl

theorem atot779 : totK PA10K2 A10K2.u779 = [0, 1188245396710, 6361263778118, 13073658819765, 12134991200914, 4811043432113, 769621354587, 36134558889, 0, 0] := by
  rw [show A10K2.u779 = KTree.node A10K2.u775 (nat_lit 12905659) (nat_lit 6846431645) (nat_lit 0) A10K2.u778 from rfl, totK_node, atot775, atot778]
  decide +kernel

theorem arows787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u787 = true := by
  rw [show A10K2.u787 = KTree.node A10K2.u783 (nat_lit 13026565) (nat_lit 7008081117) (nat_lit 0) A10K2.u786 from rfl, allE_node, arows783, irow787, arows786]
  all_goals rfl

theorem atot787 : totK PA10K2 A10K2.u787 = [0, 1147085394243, 7023576764475, 14568102692953, 11830756730239, 3303159720773, 293146761862, 5676195732, 0, 0] := by
  rw [show A10K2.u787 = KTree.node A10K2.u783 (nat_lit 13026565) (nat_lit 7008081117) (nat_lit 0) A10K2.u786 from rfl, totK_node, atot783, atot786]
  decide +kernel

theorem arows794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u794 = true := by
  rw [show A10K2.u794 = KTree.node A10K2.u790 (nat_lit 13070007) (nat_lit 14878049232) (nat_lit 0) A10K2.u793 from rfl, allE_node, arows790, irow794, arows793]
  all_goals rfl

theorem atot794 : totK PA10K2 A10K2.u794 = [847358390021, 4845422851313, 11371371316285, 13636352189636, 7594035466874, 1456032129842, 69519743899, 0, 0, 0] := by
  rw [show A10K2.u794 = KTree.node A10K2.u790 (nat_lit 13070007) (nat_lit 14878049232) (nat_lit 0) A10K2.u793 from rfl, totK_node, atot790, atot793]
  decide +kernel

theorem arows803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u803 = true := by
  rw [show A10K2.u803 = KTree.node A10K2.u799 (nat_lit 13200556) (nat_lit 8680050937) (nat_lit 0) A10K2.u802 from rfl, allE_node, arows799, irow803, arows802]
  all_goals rfl

theorem atot803 : totK PA10K2 A10K2.u803 = [1363868382074, 7731987714591, 15241535445646, 11859639891299, 3091745166835, 189380606038, 0, 0, 0, 0] := by
  rw [show A10K2.u803 = KTree.node A10K2.u799 (nat_lit 13200556) (nat_lit 8680050937) (nat_lit 0) A10K2.u802 from rfl, totK_node, atot799, atot802]
  decide +kernel

theorem arows810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u810 = true := by
  rw [show A10K2.u810 = KTree.node A10K2.u806 (nat_lit 13232050) (nat_lit 14749752711) (nat_lit 0) A10K2.u809 from rfl, allE_node, arows806, irow810, arows809]
  all_goals rfl

theorem atot810 : totK PA10K2 A10K2.u810 = [1334277149280, 6504008463905, 12727299502802, 12417656321155, 5503664595632, 858931330284, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u810 = KTree.node A10K2.u806 (nat_lit 13232050) (nat_lit 14749752711) (nat_lit 0) A10K2.u809 from rfl, totK_node, atot806, atot809]
  decide +kernel

theorem arows818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u818 = true := by
  rw [show A10K2.u818 = KTree.node A10K2.u814 (nat_lit 13333680) (nat_lit 10307510823) (nat_lit 0) A10K2.u817 from rfl, allE_node, arows814, irow818, arows817]
  all_goals rfl

theorem atot818 : totK PA10K2 A10K2.u818 = [912224543933, 6426901318264, 14578590985020, 13167109591645, 4483012655479, 470428696026, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u818 = KTree.node A10K2.u814 (nat_lit 13333680) (nat_lit 10307510823) (nat_lit 0) A10K2.u817 from rfl, totK_node, atot814, atot817]
  decide +kernel

theorem arows825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u825 = true := by
  rw [show A10K2.u825 = KTree.node A10K2.u821 (nat_lit 13365857) (nat_lit 5659121036) (nat_lit 0) A10K2.u824 from rfl, allE_node, arows821, irow825, arows824]
  all_goals rfl

theorem atot825 : totK PA10K2 A10K2.u825 = [0, 2017903133385, 9879031422882, 15987008504446, 9665279408296, 1822705685062, 93891684850, 0, 0, 0] := by
  rw [show A10K2.u825 = KTree.node A10K2.u821 (nat_lit 13365857) (nat_lit 5659121036) (nat_lit 0) A10K2.u824 from rfl, totK_node, atot821, atot824]
  decide +kernel

theorem arows835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u835 = true := by
  rw [show A10K2.u835 = KTree.node A10K2.u831 (nat_lit 13463624) (nat_lit 13633302853) (nat_lit 0) A10K2.u834 from rfl, allE_node, arows831, irow835, arows834]
  all_goals rfl

theorem atot835 : totK PA10K2 A10K2.u835 = [0, 1362400161870, 7472282612201, 14494897783052, 11594288589776, 3726438501466, 504564178266, 25565504801, 0, 0] := by
  rw [show A10K2.u835 = KTree.node A10K2.u831 (nat_lit 13463624) (nat_lit 13633302853) (nat_lit 0) A10K2.u834 from rfl, totK_node, atot831, atot834]
  decide +kernel

theorem arows842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u842 = true := by
  rw [show A10K2.u842 = KTree.node A10K2.u838 (nat_lit 13566534) (nat_lit 13407237131) (nat_lit 0) A10K2.u841 from rfl, allE_node, arows838, irow842, arows841]
  all_goals rfl

theorem atot842 : totK PA10K2 A10K2.u842 = [0, 1379063981620, 7481913630357, 14419282326182, 11811127614361, 3902810742328, 441254862842, 11138589073, 0, 0] := by
  rw [show A10K2.u842 = KTree.node A10K2.u838 (nat_lit 13566534) (nat_lit 13407237131) (nat_lit 0) A10K2.u841 from rfl, totK_node, atot838, atot841]
  decide +kernel

theorem arows850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u850 = true := by
  rw [show A10K2.u850 = KTree.node A10K2.u846 (nat_lit 14155813) (nat_lit 7044702024) (nat_lit 0) A10K2.u849 from rfl, allE_node, arows846, irow850, arows849]
  all_goals rfl

theorem atot850 : totK PA10K2 A10K2.u850 = [1298386227496, 6512770636143, 12274006571278, 11795735346592, 6186619424595, 1272174726814, 68006876977, 0, 0, 0] := by
  rw [show A10K2.u850 = KTree.node A10K2.u846 (nat_lit 14155813) (nat_lit 7044702024) (nat_lit 0) A10K2.u849 from rfl, totK_node, atot846, atot849]
  decide +kernel

theorem arows857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u857 = true := by
  rw [show A10K2.u857 = KTree.node A10K2.u853 (nat_lit 14188608) (nat_lit 15519450914) (nat_lit 0) A10K2.u856 from rfl, allE_node, arows853, irow857, arows856]
  all_goals rfl

theorem atot857 : totK PA10K2 A10K2.u857 = [828922211760, 5536387207393, 13499922236558, 13518195591131, 5099079720681, 701110297025, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u857 = KTree.node A10K2.u853 (nat_lit 14188608) (nat_lit 15519450914) (nat_lit 0) A10K2.u856 from rfl, totK_node, atot853, atot856]
  decide +kernel

theorem arows866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u866 = true := by
  rw [show A10K2.u866 = KTree.node A10K2.u862 (nat_lit 14235073) (nat_lit 5356557190) (nat_lit 0) A10K2.u865 from rfl, allE_node, arows862, irow866, arows865]
  all_goals rfl

theorem atot866 : totK PA10K2 A10K2.u866 = [1876293614846, 9097711771058, 15321581954655, 10614341404641, 2880553641796, 269989208338, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u866 = KTree.node A10K2.u862 (nat_lit 14235073) (nat_lit 5356557190) (nat_lit 0) A10K2.u865 from rfl, totK_node, atot862, atot865]
  decide +kernel

theorem arows873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u873 = true := by
  rw [show A10K2.u873 = KTree.node A10K2.u869 (nat_lit 14271710) (nat_lit 11241406203) (nat_lit 0) A10K2.u872 from rfl, allE_node, arows869, irow873, arows872]
  all_goals rfl

theorem atot873 : totK PA10K2 A10K2.u873 = [766127300133, 5175767189548, 13015881421945, 14078287581895, 5773952105176, 777401860546, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u873 = KTree.node A10K2.u869 (nat_lit 14271710) (nat_lit 11241406203) (nat_lit 0) A10K2.u872 from rfl, totK_node, atot869, atot872]
  decide +kernel

theorem arows881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u881 = true := by
  rw [show A10K2.u881 = KTree.node A10K2.u877 (nat_lit 14377022) (nat_lit 15643009357) (nat_lit 0) A10K2.u880 from rfl, allE_node, arows877, irow881, arows880]
  all_goals rfl

theorem atot881 : totK PA10K2 A10K2.u881 = [1622710366237, 8645411519572, 15704828567073, 10792369715491, 2390895245377, 138617156438, 0, 0, 0, 0] := by
  rw [show A10K2.u881 = KTree.node A10K2.u877 (nat_lit 14377022) (nat_lit 15643009357) (nat_lit 0) A10K2.u880 from rfl, totK_node, atot877, atot880]
  decide +kernel

theorem arows888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u888 = true := by
  rw [show A10K2.u888 = KTree.node A10K2.u884 (nat_lit 14399122) (nat_lit 15756248381) (nat_lit 0) A10K2.u887 from rfl, allE_node, arows884, irow888, arows887]
  all_goals rfl

theorem atot888 : totK PA10K2 A10K2.u888 = [0, 2088781346096, 10172677994436, 16278217390777, 9259395843437, 1462481219995, 37751669437, 0, 0, 0] := by
  rw [show A10K2.u888 = KTree.node A10K2.u884 (nat_lit 14399122) (nat_lit 15756248381) (nat_lit 0) A10K2.u887 from rfl, totK_node, atot884, atot887]
  decide +kernel

theorem arows899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u899 = true := by
  rw [show A10K2.u899 = KTree.node A10K2.u895 (nat_lit 14436920) (nat_lit 13369995037) (nat_lit 0) A10K2.u898 from rfl, allE_node, arows895, irow899, arows898]
  all_goals rfl

theorem atot899 : totK PA10K2 A10K2.u899 = [0, 2125305813045, 9888485772006, 15739013619808, 9640250119706, 1960309669421, 98832880381, 0, 0, 0] := by
  rw [show A10K2.u899 = KTree.node A10K2.u895 (nat_lit 14436920) (nat_lit 13369995037) (nat_lit 0) A10K2.u898 from rfl, totK_node, atot895, atot898]
  decide +kernel

theorem arows906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u906 = true := by
  rw [show A10K2.u906 = KTree.node A10K2.u902 (nat_lit 14475841) (nat_lit 10255488803) (nat_lit 0) A10K2.u905 from rfl, allE_node, arows902, irow906, arows905]
  all_goals rfl

theorem atot906 : totK PA10K2 A10K2.u906 = [0, 780638625629, 5718026812548, 14033179273698, 13577444755471, 4618497026944, 477246512407, 7007974415, 0, 0] := by
  rw [show A10K2.u906 = KTree.node A10K2.u902 (nat_lit 14475841) (nat_lit 10255488803) (nat_lit 0) A10K2.u905 from rfl, totK_node, atot902, atot905]
  decide +kernel

theorem arows914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u914 = true := by
  rw [show A10K2.u914 = KTree.node A10K2.u910 (nat_lit 14515868) (nat_lit 8653574846) (nat_lit 0) A10K2.u913 from rfl, allE_node, arows910, irow914, arows913]
  all_goals rfl

theorem atot914 : totK PA10K2 A10K2.u914 = [0, 1093657370475, 6703777540484, 14545031154960, 12999479271855, 4229916224549, 416549169714, 7151180950, 0, 0] := by
  rw [show A10K2.u914 = KTree.node A10K2.u910 (nat_lit 14515868) (nat_lit 8653574846) (nat_lit 0) A10K2.u913 from rfl, totK_node, atot910, atot913]
  decide +kernel

theorem arows921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u921 = true := by
  rw [show A10K2.u921 = KTree.node A10K2.u917 (nat_lit 14624609) (nat_lit 13652359) (nat_lit 0) A10K2.u920 from rfl, allE_node, arows917, irow921, arows920]
  all_goals rfl

theorem atot921 : totK PA10K2 A10K2.u921 = [0, 2385852921668, 10635340773929, 15817734485728, 8874050878071, 1655124188381, 74643133039, 0, 0, 0] := by
  rw [show A10K2.u921 = KTree.node A10K2.u917 (nat_lit 14624609) (nat_lit 13652359) (nat_lit 0) A10K2.u920 from rfl, totK_node, atot917, atot920]
  decide +kernel

theorem arows930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u930 = true := by
  rw [show A10K2.u930 = KTree.node A10K2.u926 (nat_lit 14654849) (nat_lit 10069016202) (nat_lit 0) A10K2.u929 from rfl, allE_node, arows926, irow930, arows929]
  all_goals rfl

theorem atot930 : totK PA10K2 A10K2.u930 = [0, 0, 3192190233118, 12929063103881, 16188619417158, 6439037295205, 658963546981, 12758098799, 0, 0] := by
  rw [show A10K2.u930 = KTree.node A10K2.u926 (nat_lit 14654849) (nat_lit 10069016202) (nat_lit 0) A10K2.u929 from rfl, totK_node, atot926, atot929]
  decide +kernel

theorem arows937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u937 = true := by
  rw [show A10K2.u937 = KTree.node A10K2.u933 (nat_lit 14684602) (nat_lit 11440571430) (nat_lit 0) A10K2.u936 from rfl, allE_node, arows933, irow937, arows936]
  all_goals rfl

theorem atot937 : totK PA10K2 A10K2.u937 = [0, 1942436274614, 8357238678965, 13022122482516, 9742545858773, 4549365975744, 997997424368, 61018386929, 0, 0] := by
  rw [show A10K2.u937 = KTree.node A10K2.u933 (nat_lit 14684602) (nat_lit 11440571430) (nat_lit 0) A10K2.u936 from rfl, totK_node, atot933, atot936]
  decide +kernel

theorem arows945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u945 = true := by
  rw [show A10K2.u945 = KTree.node A10K2.u941 (nat_lit 14716486) (nat_lit 14783533782) (nat_lit 0) A10K2.u944 from rfl, allE_node, arows941, irow945, arows944]
  all_goals rfl

theorem atot945 : totK PA10K2 A10K2.u945 = [0, 357966842975, 4136586434407, 12598206806529, 14572022817648, 6080710778149, 872235935384, 36196801203, 0, 0] := by
  rw [show A10K2.u945 = KTree.node A10K2.u941 (nat_lit 14716486) (nat_lit 14783533782) (nat_lit 0) A10K2.u944 from rfl, totK_node, atot941, atot944]
  decide +kernel

theorem arows952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u952 = true := by
  rw [show A10K2.u952 = KTree.node A10K2.u948 (nat_lit 14818358) (nat_lit 16232272249) (nat_lit 0) A10K2.u951 from rfl, allE_node, arows948, irow952, arows951]
  all_goals rfl

theorem atot952 : totK PA10K2 A10K2.u952 = [0, 1534855864381, 8406438656363, 15577243581330, 10851841596427, 2462471662853, 146093869612, 0, 0, 0] := by
  rw [show A10K2.u952 = KTree.node A10K2.u948 (nat_lit 14818358) (nat_lit 16232272249) (nat_lit 0) A10K2.u951 from rfl, totK_node, atot948, atot951]
  decide +kernel

theorem arows962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u962 = true := by
  rw [show A10K2.u962 = KTree.node A10K2.u958 (nat_lit 14880441) (nat_lit 5769029828) (nat_lit 0) A10K2.u961 from rfl, allE_node, arows958, irow962, arows961]
  all_goals rfl

theorem atot962 : totK PA10K2 A10K2.u962 = [0, 1646017373460, 8115217864499, 14676260838998, 11244912926274, 3100574424035, 274460011689, 5976421810, 0, 0] := by
  rw [show A10K2.u962 = KTree.node A10K2.u958 (nat_lit 14880441) (nat_lit 5769029828) (nat_lit 0) A10K2.u961 from rfl, totK_node, atot958, atot961]
  decide +kernel

theorem arows969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u969 = true := by
  rw [show A10K2.u969 = KTree.node A10K2.u965 (nat_lit 14912620) (nat_lit 8765971115) (nat_lit 0) A10K2.u968 from rfl, allE_node, arows965, irow969, arows968]
  all_goals rfl

theorem atot969 : totK PA10K2 A10K2.u969 = [0, 576020245237, 4641208829379, 12831569387188, 14616894051764, 6291070462899, 735102524435, 13671283666, 0, 0] := by
  rw [show A10K2.u969 = KTree.node A10K2.u965 (nat_lit 14912620) (nat_lit 8765971115) (nat_lit 0) A10K2.u968 from rfl, totK_node, atot965, atot968]
  decide +kernel

theorem arows977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u977 = true := by
  rw [show A10K2.u977 = KTree.node A10K2.u973 (nat_lit 14944916) (nat_lit 10812955462) (nat_lit 0) A10K2.u976 from rfl, allE_node, arows973, irow977, arows976]
  all_goals rfl

theorem atot977 : totK PA10K2 A10K2.u977 = [0, 0, 2076472589084, 9983230150981, 15786992198484, 8998784166036, 1690029446956, 91941799992, 0, 0] := by
  rw [show A10K2.u977 = KTree.node A10K2.u973 (nat_lit 14944916) (nat_lit 10812955462) (nat_lit 0) A10K2.u976 from rfl, totK_node, atot973, atot976]
  decide +kernel

theorem arows984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u984 = true := by
  rw [show A10K2.u984 = KTree.node A10K2.u980 (nat_lit 14977089) (nat_lit 10335345372) (nat_lit 0) A10K2.u983 from rfl, allE_node, arows980, irow984, arows983]
  all_goals rfl

theorem atot984 : totK PA10K2 A10K2.u984 = [0, 0, 799225256197, 5957831366479, 14428718740936, 13223328743652, 4019401250185, 405763424796, 7237400819, 0] := by
  rw [show A10K2.u984 = KTree.node A10K2.u980 (nat_lit 14977089) (nat_lit 10335345372) (nat_lit 0) A10K2.u983 from rfl, totK_node, atot980, atot983]
  decide +kernel

theorem arows993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u993 = true := by
  rw [show A10K2.u993 = KTree.node A10K2.u989 (nat_lit 15091818) (nat_lit 5611279770) (nat_lit 0) A10K2.u992 from rfl, allE_node, arows989, irow993, arows992]
  all_goals rfl

theorem atot993 : totK PA10K2 A10K2.u993 = [0, 0, 2335330790953, 10841395917125, 16170627937735, 8007838596233, 1247396563945, 53298669188, 0, 0] := by
  rw [show A10K2.u993 = KTree.node A10K2.u989 (nat_lit 15091818) (nat_lit 5611279770) (nat_lit 0) A10K2.u992 from rfl, totK_node, atot989, atot992]
  decide +kernel

theorem arows1000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1000 = true := by
  rw [show A10K2.u1000 = KTree.node A10K2.u996 (nat_lit 15167560) (nat_lit 13784267902) (nat_lit 0) A10K2.u999 from rfl, allE_node, arows996, irow1000, arows999]
  all_goals rfl

theorem atot1000 : totK PA10K2 A10K2.u1000 = [0, 847358390021, 4917663728651, 11447117245911, 13517149498525, 7478482603598, 1398562231996, 69229008279, 0, 0] := by
  rw [show A10K2.u1000 = KTree.node A10K2.u996 (nat_lit 15167560) (nat_lit 13784267902) (nat_lit 0) A10K2.u999 from rfl, totK_node, atot996, atot999]
  decide +kernel

theorem arows1008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1008 = true := by
  rw [show A10K2.u1008 = KTree.node A10K2.u1004 (nat_lit 15298161) (nat_lit 7697415613) (nat_lit 0) A10K2.u1007 from rfl, allE_node, arows1004, irow1008, arows1007]
  all_goals rfl

theorem atot1008 : totK PA10K2 A10K2.u1008 = [0, 1363868382074, 7657258626516, 15024744345383, 11686420290052, 3298714797522, 355892802866, 20331139758, 0, 0] := by
  rw [show A10K2.u1008 = KTree.node A10K2.u1004 (nat_lit 15298161) (nat_lit 7697415613) (nat_lit 0) A10K2.u1007 from rfl, totK_node, atot1004, atot1007]
  decide +kernel

theorem arows1015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1015 = true := by
  rw [show A10K2.u1015 = KTree.node A10K2.u1011 (nat_lit 15330766) (nat_lit 14819004796) (nat_lit 0) A10K2.u1014 from rfl, allE_node, arows1011, irow1015, arows1014]
  all_goals rfl

theorem atot1015 : totK PA10K2 A10K2.u1015 = [0, 1379554642640, 7015575070213, 13463652990948, 12066649248566, 4820283183087, 638215151386, 16637449799, 0, 0] := by
  rw [show A10K2.u1015 = KTree.node A10K2.u1011 (nat_lit 15330766) (nat_lit 14819004796) (nat_lit 0) A10K2.u1014 from rfl, totK_node, atot1011, atot1014]
  decide +kernel

theorem arows1029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1029 = true := by
  rw [show A10K2.u1029 = KTree.node A10K2.u1025 (nat_lit 15431387) (nat_lit 6962742351) (nat_lit 0) A10K2.u1028 from rfl, allE_node, arows1025, irow1029, arows1028]
  all_goals rfl

theorem atot1029 : totK PA10K2 A10K2.u1029 = [0, 866947050573, 6129932448844, 14460382809070, 13470179809978, 4496638221045, 414876983953, 6632180018, 0, 0] := by
  rw [show A10K2.u1029 = KTree.node A10K2.u1025 (nat_lit 15431387) (nat_lit 6962742351) (nat_lit 0) A10K2.u1028 from rfl, totK_node, atot1025, atot1028]
  decide +kernel

theorem arows1036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1036 = true := by
  rw [show A10K2.u1036 = KTree.node A10K2.u1032 (nat_lit 15463931) (nat_lit 6247617231) (nat_lit 0) A10K2.u1035 from rfl, allE_node, arows1032, irow1036, arows1035]
  all_goals rfl

theorem atot1036 : totK PA10K2 A10K2.u1036 = [0, 0, 1797647175831, 9337861069454, 16030283914786, 10125833997605, 1937544585123, 99700941423, 0, 0] := by
  rw [show A10K2.u1036 = KTree.node A10K2.u1032 (nat_lit 15463931) (nat_lit 6247617231) (nat_lit 0) A10K2.u1035 from rfl, totK_node, atot1032, atot1035]
  decide +kernel

theorem arows1044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1044 = true := by
  rw [show A10K2.u1044 = KTree.node A10K2.u1040 (nat_lit 15562083) (nat_lit 9354519032) (nat_lit 0) A10K2.u1043 from rfl, allE_node, arows1040, irow1044, arows1043]
  all_goals rfl

theorem atot1044 : totK PA10K2 A10K2.u1044 = [0, 0, 1362400161870, 7452378557215, 14564352599109, 11737100077106, 3640040356056, 383653286466, 7380853412, 0] := by
  rw [show A10K2.u1044 = KTree.node A10K2.u1040 (nat_lit 15562083) (nat_lit 9354519032) (nat_lit 0) A10K2.u1043 from rfl, totK_node, atot1040, atot1043]
  decide +kernel

theorem arows1051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1051 = true := by
  rw [show A10K2.u1051 = KTree.node A10K2.u1047 (nat_lit 15672478) (nat_lit 14834970983) (nat_lit 0) A10K2.u1050 from rfl, allE_node, arows1047, irow1051, arows1050]
  all_goals rfl

theorem atot1051 : totK PA10K2 A10K2.u1051 = [0, 0, 2058041869986, 9789606427937, 16002888201925, 9995841616182, 1844732123130, 75040286064, 0, 0] := by
  rw [show A10K2.u1051 = KTree.node A10K2.u1047 (nat_lit 15672478) (nat_lit 14834970983) (nat_lit 0) A10K2.u1050 from rfl, totK_node, atot1047, atot1050]
  decide +kernel

theorem arows1060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1060 = true := by
  rw [show A10K2.u1060 = KTree.node A10K2.u1056 (nat_lit 16257086) (nat_lit 15375569526) (nat_lit 0) A10K2.u1059 from rfl, allE_node, arows1056, irow1060, arows1059]
  all_goals rfl

theorem atot1060 : totK PA10K2 A10K2.u1060 = [0, 2127308439256, 8791358856389, 13112685624212, 9571602078270, 4634283271463, 1032361757899, 62382159641, 0, 0] := by
  rw [show A10K2.u1060 = KTree.node A10K2.u1056 (nat_lit 16257086) (nat_lit 15375569526) (nat_lit 0) A10K2.u1059 from rfl, totK_node, atot1056, atot1059]
  decide +kernel

theorem arows1067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1067 = true := by
  rw [show A10K2.u1067 = KTree.node A10K2.u1063 (nat_lit 16290302) (nat_lit 13432087526) (nat_lit 0) A10K2.u1066 from rfl, allE_node, arows1063, irow1067, arows1066]
  all_goals rfl

theorem atot1067 : totK PA10K2 A10K2.u1067 = [0, 77065070666, 3503390029388, 13138016636245, 15857608397788, 6146617357859, 671981650640, 12477124820, 0, 0] := by
  rw [show A10K2.u1067 = KTree.node A10K2.u1063 (nat_lit 16290302) (nat_lit 13432087526) (nat_lit 0) A10K2.u1066 from rfl, totK_node, atot1063, atot1066]
  decide +kernel

theorem arows1075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1075 = true := by
  rw [show A10K2.u1075 = KTree.node A10K2.u1071 (nat_lit 16343652) (nat_lit 8074799477) (nat_lit 0) A10K2.u1074 from rfl, allE_node, arows1071, irow1075, arows1074]
  all_goals rfl

theorem atot1075 : totK PA10K2 A10K2.u1075 = [0, 1799228544180, 9214943463332, 15873396483500, 10512375601868, 2302556907167, 126592791157, 0, 0, 0] := by
  rw [show A10K2.u1075 = KTree.node A10K2.u1071 (nat_lit 16343652) (nat_lit 8074799477) (nat_lit 0) A10K2.u1074 from rfl, totK_node, atot1071, atot1074]
  decide +kernel

theorem arows1082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1082 = true := by
  rw [show A10K2.u1082 = KTree.node A10K2.u1078 (nat_lit 16379547) (nat_lit 9863270284) (nat_lit 0) A10K2.u1081 from rfl, allE_node, arows1078, irow1082, arows1081]
  all_goals rfl

theorem atot1082 : totK PA10K2 A10K2.u1082 = [0, 1344456871382, 6767295003896, 13291957180835, 12342042142214, 4897118961397, 592632609412, 12696458652, 0, 0] := by
  rw [show A10K2.u1082 = KTree.node A10K2.u1078 (nat_lit 16379547) (nat_lit 9863270284) (nat_lit 0) A10K2.u1081 from rfl, totK_node, atot1078, atot1081]
  decide +kernel

theorem arows1092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1092 = true := by
  rw [show A10K2.u1092 = KTree.node A10K2.u1088 (nat_lit 16478984) (nat_lit 12371991347) (nat_lit 0) A10K2.u1091 from rfl, allE_node, arows1088, irow1092, arows1091]
  all_goals rfl

theorem atot1092 : totK PA10K2 A10K2.u1092 = [0, 1029302401414, 6582943738937, 14356791452159, 12847010169587, 4266851624635, 400255095164, 6904928264, 0, 0] := by
  rw [show A10K2.u1092 = KTree.node A10K2.u1088 (nat_lit 16478984) (nat_lit 12371991347) (nat_lit 0) A10K2.u1091 from rfl, totK_node, atot1088, atot1091]
  decide +kernel

theorem arows1099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1099 = true := by
  rw [show A10K2.u1099 = KTree.node A10K2.u1095 (nat_lit 16510648) (nat_lit 11391076101) (nat_lit 0) A10K2.u1098 from rfl, allE_node, arows1095, irow1099, arows1098]
  all_goals rfl

theorem atot1099 : totK PA10K2 A10K2.u1099 = [0, 0, 2323662557225, 10546712259329, 15788927336618, 8872291112299, 1611300823233, 80634276378, 0, 0] := by
  rw [show A10K2.u1099 = KTree.node A10K2.u1095 (nat_lit 16510648) (nat_lit 11391076101) (nat_lit 0) A10K2.u1098 from rfl, totK_node, atot1095, atot1098]
  decide +kernel

theorem arows1107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1107 = true := by
  rw [show A10K2.u1107 = KTree.node A10K2.u1103 (nat_lit 16544197) (nat_lit 4787498862) (nat_lit 0) A10K2.u1106 from rfl, allE_node, arows1103, irow1107, arows1106]
  all_goals rfl

theorem atot1107 : totK PA10K2 A10K2.u1107 = [0, 0, 1304415440809, 7384459507519, 14839369864708, 12061528024557, 3465120148525, 305829260107, 6725424603, 0] := by
  rw [show A10K2.u1107 = KTree.node A10K2.u1103 (nat_lit 16544197) (nat_lit 4787498862) (nat_lit 0) A10K2.u1106 from rfl, totK_node, atot1103, atot1106]
  decide +kernel

theorem arows1114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1114 = true := by
  rw [show A10K2.u1114 = KTree.node A10K2.u1110 (nat_lit 16594398) (nat_lit 14491109585) (nat_lit 0) A10K2.u1113 from rfl, allE_node, arows1110, irow1114, arows1113]
  all_goals rfl

theorem atot1114 : totK PA10K2 A10K2.u1114 = [0, 0, 1872518455458, 9405743070824, 16133863237489, 10341137185504, 1957684621762, 87468490529, 0, 0] := by
  rw [show A10K2.u1114 = KTree.node A10K2.u1110 (nat_lit 16594398) (nat_lit 14491109585) (nat_lit 0) A10K2.u1113 from rfl, totK_node, atot1110, atot1113]
  decide +kernel

theorem arows1123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1123 = true := by
  rw [show A10K2.u1123 = KTree.node A10K2.u1119 (nat_lit 16638512) (nat_lit 14770524562) (nat_lit 0) A10K2.u1122 from rfl, allE_node, arows1119, irow1123, arows1122]
  all_goals rfl

theorem atot1123 : totK PA10K2 A10K2.u1123 = [0, 0, 760685406009, 5803675197976, 14336668061246, 13817811059273, 4408800062656, 391096746565, 6860445330, 0] := by
  rw [show A10K2.u1123 = KTree.node A10K2.u1119 (nat_lit 16638512) (nat_lit 14770524562) (nat_lit 0) A10K2.u1122 from rfl, totK_node, atot1119, atot1122]
  decide +kernel

theorem arows1130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1130 = true := by
  rw [show A10K2.u1130 = KTree.node A10K2.u1126 (nat_lit 16739564) (nat_lit 6676469903) (nat_lit 0) A10K2.u1129 from rfl, allE_node, arows1126, irow1130, arows1129]
  all_goals rfl

theorem atot1130 : totK PA10K2 A10K2.u1130 = [0, 0, 1618449319945, 8305093929763, 15126525070911, 11319046325681, 2768559376542, 161583035750, 0, 0] := by
  rw [show A10K2.u1130 = KTree.node A10K2.u1126 (nat_lit 16739564) (nat_lit 6676469903) (nat_lit 0) A10K2.u1129 from rfl, totK_node, atot1126, atot1129]
  decide +kernel

theorem arows1138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1138 = true := by
  rw [show A10K2.u1138 = KTree.node A10K2.u1134 (nat_lit 16770962) (nat_lit 15452378084) (nat_lit 0) A10K2.u1137 from rfl, allE_node, arows1134, irow1138, arows1137]
  all_goals rfl

theorem atot1138 : totK PA10K2 A10K2.u1138 = [0, 874031059315, 3015030631522, 4604777366696, 8629101414633, 12792383579470, 7570453242822, 1456237671250, 73776485728, 0] := by
  rw [show A10K2.u1138 = KTree.node A10K2.u1134 (nat_lit 16770962) (nat_lit 15452378084) (nat_lit 0) A10K2.u1137 from rfl, totK_node, atot1134, atot1137]
  decide +kernel

theorem arows1145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1145 = true := by
  rw [show A10K2.u1145 = KTree.node A10K2.u1141 (nat_lit 16800407) (nat_lit 2790686487) (nat_lit 0) A10K2.u1144 from rfl, allE_node, arows1141, irow1145, arows1144]
  all_goals rfl

theorem atot1145 : totK PA10K2 A10K2.u1145 = [0, 1506004337164, 8479731132485, 15749759671130, 10714268396809, 2292254183907, 116738531973, 0, 0, 0] := by
  rw [show A10K2.u1145 = KTree.node A10K2.u1141 (nat_lit 16800407) (nat_lit 2790686487) (nat_lit 0) A10K2.u1144 from rfl, totK_node, atot1141, atot1144]
  decide +kernel

theorem arows1156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1156 = true := by
  rw [show A10K2.u1156 = KTree.node A10K2.u1152 (nat_lit 16830791) (nat_lit 5686307712) (nat_lit 0) A10K2.u1155 from rfl, allE_node, arows1152, irow1156, arows1155]
  all_goals rfl

theorem atot1156 : totK PA10K2 A10K2.u1156 = [0, 801319042366, 4985043675523, 12231160350089, 13653715452828, 5873688050929, 854474320434, 36196801203, 0, 0] := by
  rw [show A10K2.u1156 = KTree.node A10K2.u1152 (nat_lit 16830791) (nat_lit 5686307712) (nat_lit 0) A10K2.u1155 from rfl, totK_node, atot1152, atot1155]
  decide +kernel

theorem arows1163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1163 = true := by
  rw [show A10K2.u1163 = KTree.node A10K2.u1159 (nat_lit 16926783) (nat_lit 8444205577) (nat_lit 0) A10K2.u1162 from rfl, allE_node, arows1159, irow1163, arows1162]
  all_goals rfl

theorem atot1163 : totK PA10K2 A10K2.u1163 = [0, 1199240304554, 7479730070985, 15181487330664, 11093843412460, 2311916838817, 99278582060, 0, 0, 0] := by
  rw [show A10K2.u1163 = KTree.node A10K2.u1159 (nat_lit 16926783) (nat_lit 8444205577) (nat_lit 0) A10K2.u1162 from rfl, totK_node, atot1159, atot1162]
  decide +kernel

theorem arows1171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1171 = true := by
  rw [show A10K2.u1171 = KTree.node A10K2.u1167 (nat_lit 16977520) (nat_lit 14750590265) (nat_lit 0) A10K2.u1170 from rfl, allE_node, arows1167, irow1171, arows1170]
  all_goals rfl

theorem atot1171 : totK PA10K2 A10K2.u1171 = [0, 1804732975140, 8460204626957, 14466653270516, 10770182244205, 3057834570011, 304119351963, 6354482628, 0, 0] := by
  rw [show A10K2.u1171 = KTree.node A10K2.u1167 (nat_lit 16977520) (nat_lit 14750590265) (nat_lit 0) A10K2.u1170 from rfl, totK_node, atot1167, atot1170]
  decide +kernel

theorem arows1178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1178 = true := by
  rw [show A10K2.u1178 = KTree.node A10K2.u1174 (nat_lit 17010353) (nat_lit 6553012740) (nat_lit 0) A10K2.u1177 from rfl, allE_node, arows1174, irow1178, arows1177]
  all_goals rfl

theorem atot1178 : totK PA10K2 A10K2.u1178 = [0, 323642880550, 4169983820009, 13180693142682, 15336406353143, 6203967483676, 626251608089, 6904928264, 0, 0] := by
  rw [show A10K2.u1178 = KTree.node A10K2.u1174 (nat_lit 17010353) (nat_lit 6553012740) (nat_lit 0) A10K2.u1177 from rfl, totK_node, atot1174, atot1177]
  decide +kernel

theorem arows1187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1187 = true := by
  rw [show A10K2.u1187 = KTree.node A10K2.u1183 (nat_lit 17043513) (nat_lit 7330973663) (nat_lit 0) A10K2.u1186 from rfl, allE_node, arows1183, irow1187, arows1186]
  all_goals rfl

theorem atot1187 : totK PA10K2 A10K2.u1187 = [0, 0, 1960347968142, 9530625500929, 15588971079849, 9327064898134, 1769386833338, 83867732211, 0, 0] := by
  rw [show A10K2.u1187 = KTree.node A10K2.u1183 (nat_lit 17043513) (nat_lit 7330973663) (nat_lit 0) A10K2.u1186 from rfl, totK_node, atot1183, atot1186]
  decide +kernel

theorem arows1194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1194 = true := by
  rw [show A10K2.u1194 = KTree.node A10K2.u1190 (nat_lit 17075585) (nat_lit 10144077097) (nat_lit 0) A10K2.u1193 from rfl, allE_node, arows1190, irow1194, arows1193]
  all_goals rfl

theorem atot1194 : totK PA10K2 A10K2.u1194 = [0, 0, 581035684948, 4728433694788, 12795099315649, 13812680505615, 5431757449172, 744855637404, 30605747850, 0] := by
  rw [show A10K2.u1194 = KTree.node A10K2.u1190 (nat_lit 17075585) (nat_lit 10144077097) (nat_lit 0) A10K2.u1193 from rfl, totK_node, atot1190, atot1193]
  decide +kernel

theorem arows1202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1202 = true := by
  rw [show A10K2.u1202 = KTree.node A10K2.u1198 (nat_lit 17177358) (nat_lit 7411613744) (nat_lit 0) A10K2.u1201 from rfl, allE_node, arows1198, irow1202, arows1201]
  all_goals rfl

theorem atot1202 : totK PA10K2 A10K2.u1202 = [0, 0, 1999433227150, 9819012585269, 15578700966770, 8678461539158, 1685298392241, 174343482561, 5528811039, 0] := by
  rw [show A10K2.u1202 = KTree.node A10K2.u1198 (nat_lit 17177358) (nat_lit 7411613744) (nat_lit 0) A10K2.u1201 from rfl, totK_node, atot1198, atot1201]
  decide +kernel

theorem arows1209 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1209 = true := by
  rw [show A10K2.u1209 = KTree.node A10K2.u1205 (nat_lit 17222314) (nat_lit 12523120418) (nat_lit 0) A10K2.u1208 from rfl, allE_node, arows1205, irow1209, arows1208]
  all_goals rfl

theorem atot1209 : totK PA10K2 A10K2.u1209 = [0, 0, 999439602828, 6382360376909, 14413737269454, 12333807959194, 3323139272924, 299386562071, 5676195732, 0] := by
  rw [show A10K2.u1209 = KTree.node A10K2.u1205 (nat_lit 17222314) (nat_lit 12523120418) (nat_lit 0) A10K2.u1208 from rfl, totK_node, atot1205, atot1208]
  decide +kernel

theorem arows1219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1219 = true := by
  rw [show A10K2.u1219 = KTree.node A10K2.u1215 (nat_lit 17267719) (nat_lit 14175392568) (nat_lit 0) A10K2.u1218 from rfl, allE_node, arows1215, irow1219, arows1218]
  all_goals rfl

theorem atot1219 : totK PA10K2 A10K2.u1219 = [0, 1054409893898, 5556264290195, 12071741301865, 13084015853772, 6510151128596, 1168297780519, 48270752734, 0, 0] := by
  rw [show A10K2.u1219 = KTree.node A10K2.u1215 (nat_lit 17267719) (nat_lit 14175392568) (nat_lit 0) A10K2.u1218 from rfl, totK_node, atot1215, atot1218]
  decide +kernel

theorem arows1226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1226 = true := by
  rw [show A10K2.u1226 = KTree.node A10K2.u1222 (nat_lit 17855026) (nat_lit 9779337032) (nat_lit 0) A10K2.u1225 from rfl, allE_node, arows1222, irow1226, arows1225]
  all_goals rfl

theorem atot1226 : totK PA10K2 A10K2.u1226 = [0, 1137063831772, 6793413699443, 13885957284426, 11820230706109, 4317613010423, 635544363305, 30650496230, 0, 0] := by
  rw [show A10K2.u1226 = KTree.node A10K2.u1222 (nat_lit 17855026) (nat_lit 9779337032) (nat_lit 0) A10K2.u1225 from rfl, totK_node, atot1222, atot1225]
  decide +kernel

theorem arows1234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1234 = true := by
  rw [show A10K2.u1234 = KTree.node A10K2.u1230 (nat_lit 17901459) (nat_lit 10671537095) (nat_lit 0) A10K2.u1233 from rfl, allE_node, arows1230, irow1234, arows1233]
  all_goals rfl

theorem atot1234 : totK PA10K2 A10K2.u1234 = [0, 1301904005721, 7282583153545, 14378396457445, 11516792162603, 3435787391425, 305701275290, 5546304973, 0, 0] := by
  rw [show A10K2.u1234 = KTree.node A10K2.u1230 (nat_lit 17901459) (nat_lit 10671537095) (nat_lit 0) A10K2.u1233 from rfl, totK_node, atot1230, atot1233]
  decide +kernel

theorem arows1241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1241 = true := by
  rw [show A10K2.u1241 = KTree.node A10K2.u1237 (nat_lit 17958916) (nat_lit 12641517020) (nat_lit 0) A10K2.u1240 from rfl, allE_node, arows1237, irow1241, arows1240]
  all_goals rfl

theorem atot1241 : totK PA10K2 A10K2.u1241 = [0, 1351212383076, 7175019827997, 14016247015934, 11587678565562, 3484989760565, 333621009683, 6121173289, 0, 0] := by
  rw [show A10K2.u1241 = KTree.node A10K2.u1237 (nat_lit 17958916) (nat_lit 12641517020) (nat_lit 0) A10K2.u1240 from rfl, totK_node, atot1237, atot1240]
  decide +kernel

theorem arows1250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1250 = true := by
  rw [show A10K2.u1250 = KTree.node A10K2.u1246 (nat_lit 17991737) (nat_lit 7197847521) (nat_lit 0) A10K2.u1249 from rfl, allE_node, arows1246, irow1250, arows1249]
  all_goals rfl

theorem atot1250 : totK PA10K2 A10K2.u1250 = [0, 821967029087, 6234945443254, 14757287873262, 12475413439294, 3030583036216, 180525562015, 0, 0, 0] := by
  rw [show A10K2.u1250 = KTree.node A10K2.u1246 (nat_lit 17991737) (nat_lit 7197847521) (nat_lit 0) A10K2.u1249 from rfl, totK_node, atot1246, atot1249]
  decide +kernel

theorem arows1257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1257 = true := by
  rw [show A10K2.u1257 = KTree.node A10K2.u1253 (nat_lit 18104661) (nat_lit 6864452057) (nat_lit 0) A10K2.u1256 from rfl, allE_node, arows1253, irow1257, arows1256]
  all_goals rfl

theorem atot1257 : totK PA10K2 A10K2.u1257 = [0, 0, 2191473725670, 10306444572677, 15940484397228, 8422747031729, 1315535882422, 50380680131, 0, 0] := by
  rw [show A10K2.u1257 = KTree.node A10K2.u1253 (nat_lit 18104661) (nat_lit 6864452057) (nat_lit 0) A10K2.u1256 from rfl, totK_node, atot1253, atot1256]
  decide +kernel

theorem arows1265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1265 = true := by
  rw [show A10K2.u1265 = KTree.node A10K2.u1261 (nat_lit 18174307) (nat_lit 8535951569) (nat_lit 0) A10K2.u1264 from rfl, allE_node, arows1261, irow1265, arows1264]
  all_goals rfl

theorem atot1265 : totK PA10K2 A10K2.u1265 = [0, 0, 2305953033882, 10591891033814, 15913322866470, 8008705302846, 1158485593364, 42147406732, 0, 0] := by
  rw [show A10K2.u1265 = KTree.node A10K2.u1261 (nat_lit 18174307) (nat_lit 8535951569) (nat_lit 0) A10K2.u1264 from rfl, totK_node, atot1261, atot1264]
  decide +kernel

theorem arows1272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1272 = true := by
  rw [show A10K2.u1272 = KTree.node A10K2.u1268 (nat_lit 18241687) (nat_lit 10053429044) (nat_lit 0) A10K2.u1271 from rfl, allE_node, arows1268, irow1272, arows1271]
  all_goals rfl

theorem atot1272 : totK PA10K2 A10K2.u1272 = [0, 0, 1163893791019, 7887206500688, 15936967183470, 10142599917559, 1808359251168, 80495744346, 0, 0] := by
  rw [show A10K2.u1272 = KTree.node A10K2.u1268 (nat_lit 18241687) (nat_lit 10053429044) (nat_lit 0) A10K2.u1271 from rfl, totK_node, atot1268, atot1271]
  decide +kernel

theorem arows1284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1284 = true := by
  rw [show A10K2.u1284 = KTree.node A10K2.u1280 (nat_lit 18357439) (nat_lit 14089911145) (nat_lit 0) A10K2.u1283 from rfl, allE_node, arows1280, irow1284, arows1283]
  all_goals rfl

theorem atot1284 : totK PA10K2 A10K2.u1284 = [0, 2213394006731, 9784470906116, 13985958161132, 7744393104446, 3299915828875, 1366315842711, 195382007035, 6354482628, 0] := by
  rw [show A10K2.u1284 = KTree.node A10K2.u1280 (nat_lit 18357439) (nat_lit 14089911145) (nat_lit 0) A10K2.u1283 from rfl, totK_node, atot1280, atot1283]
  decide +kernel

theorem arows1291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1291 = true := by
  rw [show A10K2.u1291 = KTree.node A10K2.u1287 (nat_lit 18389783) (nat_lit 11933677) (nat_lit 0) A10K2.u1290 from rfl, allE_node, arows1287, irow1291, arows1290]
  all_goals rfl

theorem atot1291 : totK PA10K2 A10K2.u1291 = [0, 190213598080, 3185384977423, 11963196377180, 15852653467646, 6814391519624, 939859890156, 36196801203, 0, 0] := by
  rw [show A10K2.u1291 = KTree.node A10K2.u1287 (nat_lit 18389783) (nat_lit 11933677) (nat_lit 0) A10K2.u1290 from rfl, totK_node, atot1287, atot1290]
  decide +kernel

theorem arows1299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1299 = true := by
  rw [show A10K2.u1299 = KTree.node A10K2.u1295 (nat_lit 18445553) (nat_lit 5117575968) (nat_lit 0) A10K2.u1298 from rfl, allE_node, arows1295, irow1299, arows1298]
  all_goals rfl

theorem atot1299 : totK PA10K2 A10K2.u1299 = [0, 1198523436832, 7220756142900, 15123295360119, 12915556908907, 4073133833424, 400616559167, 8047840951, 0, 0] := by
  rw [show A10K2.u1299 = KTree.node A10K2.u1295 (nat_lit 18445553) (nat_lit 5117575968) (nat_lit 0) A10K2.u1298 from rfl, totK_node, atot1295, atot1298]
  decide +kernel

theorem arows1306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1306 = true := by
  rw [show A10K2.u1306 = KTree.node A10K2.u1302 (nat_lit 18557140) (nat_lit 9419032610) (nat_lit 0) A10K2.u1305 from rfl, allE_node, arows1302, irow1306, arows1305]
  all_goals rfl

theorem atot1306 : totK PA10K2 A10K2.u1306 = [0, 2283745797574, 10317227108918, 15862626410258, 9402132989575, 1902803410689, 101730507678, 0, 0, 0] := by
  rw [show A10K2.u1306 = KTree.node A10K2.u1302 (nat_lit 18557140) (nat_lit 9419032610) (nat_lit 0) A10K2.u1305 from rfl, totK_node, atot1302, atot1305]
  decide +kernel

theorem arows1315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1315 = true := by
  rw [show A10K2.u1315 = KTree.node A10K2.u1311 (nat_lit 18589056) (nat_lit 11416795571) (nat_lit 0) A10K2.u1314 from rfl, allE_node, arows1311, irow1315, arows1314]
  all_goals rfl

theorem atot1315 : totK PA10K2 A10K2.u1315 = [0, 0, 2842636558674, 12189918878903, 16472476832712, 7344708855559, 816010359415, 13951953716, 0, 0] := by
  rw [show A10K2.u1315 = KTree.node A10K2.u1311 (nat_lit 18589056) (nat_lit 11416795571) (nat_lit 0) A10K2.u1314 from rfl, totK_node, atot1311, atot1314]
  decide +kernel

theorem arows1322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1322 = true := by
  rw [show A10K2.u1322 = KTree.node A10K2.u1318 (nat_lit 18618724) (nat_lit 13913418094) (nat_lit 0) A10K2.u1321 from rfl, allE_node, arows1318, irow1322, arows1321]
  all_goals rfl

theorem atot1322 : totK PA10K2 A10K2.u1322 = [0, 0, 2213394006731, 10064927133417, 15612230896315, 9108994202683, 1800780371946, 97595586199, 0, 0] := by
  rw [show A10K2.u1322 = KTree.node A10K2.u1318 (nat_lit 18618724) (nat_lit 13913418094) (nat_lit 0) A10K2.u1321 from rfl, totK_node, atot1318, atot1321]
  decide +kernel

theorem arows1330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1330 = true := by
  rw [show A10K2.u1330 = KTree.node A10K2.u1326 (nat_lit 18651420) (nat_lit 11301358105) (nat_lit 0) A10K2.u1329 from rfl, allE_node, arows1326, irow1330, arows1329]
  all_goals rfl

theorem atot1330 : totK PA10K2 A10K2.u1330 = [0, 0, 593578530300, 5154583263617, 14118180768758, 14455698473366, 4751653984882, 442615174252, 7007974415, 0] := by
  rw [show A10K2.u1330 = KTree.node A10K2.u1326 (nat_lit 18651420) (nat_lit 11301358105) (nat_lit 0) A10K2.u1329 from rfl, totK_node, atot1326, atot1329]
  decide +kernel

theorem arows1337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1337 = true := by
  rw [show A10K2.u1337 = KTree.node A10K2.u1333 (nat_lit 18710473) (nat_lit 5628997267) (nat_lit 0) A10K2.u1336 from rfl, allE_node, arows1333, irow1337, arows1336]
  all_goals rfl

theorem atot1337 : totK PA10K2 A10K2.u1337 = [0, 0, 2202785573803, 10259975710392, 16283569960277, 9746785521436, 1839832210144, 82403716286, 0, 0] := by
  rw [show A10K2.u1337 = KTree.node A10K2.u1333 (nat_lit 18710473) (nat_lit 5628997267) (nat_lit 0) A10K2.u1336 from rfl, totK_node, atot1333, atot1336]
  decide +kernel

theorem arows1347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1347 = true := by
  rw [show A10K2.u1347 = KTree.node A10K2.u1343 (nat_lit 18840969) (nat_lit 8901588291) (nat_lit 0) A10K2.u1346 from rfl, allE_node, arows1343, irow1347, arows1346]
  all_goals rfl

theorem atot1347 : totK PA10K2 A10K2.u1347 = [0, 0, 872630842479, 6290127430263, 14647872905558, 13391388422441, 4294612038121, 390026337921, 6318667960, 0] := by
  rw [show A10K2.u1347 = KTree.node A10K2.u1343 (nat_lit 18840969) (nat_lit 8901588291) (nat_lit 0) A10K2.u1346 from rfl, totK_node, atot1343, atot1346]
  decide +kernel

theorem arows1354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1354 = true := by
  rw [show A10K2.u1354 = KTree.node A10K2.u1350 (nat_lit 18877477) (nat_lit 6724379814) (nat_lit 0) A10K2.u1353 from rfl, allE_node, arows1350, irow1354, arows1353]
  all_goals rfl

theorem atot1354 : totK PA10K2 A10K2.u1354 = [0, 0, 1589972518608, 7833170902776, 13834458494965, 10657594889522, 4089595025422, 701215296143, 35562304373, 0] := by
  rw [show A10K2.u1354 = KTree.node A10K2.u1350 (nat_lit 18877477) (nat_lit 6724379814) (nat_lit 0) A10K2.u1353 from rfl, totK_node, atot1350, atot1353]
  decide +kernel

theorem arows1362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1362 = true := by
  rw [show A10K2.u1362 = KTree.node A10K2.u1358 (nat_lit 18907757) (nat_lit 5300881204) (nat_lit 0) A10K2.u1361 from rfl, allE_node, arows1358, irow1362, arows1361]
  all_goals rfl

theorem atot1362 : totK PA10K2 A10K2.u1362 = [0, 0, 777444773176, 5419831271287, 13452774789332, 13322575867704, 4761360400728, 661248529519, 30650496230, 0] := by
  rw [show A10K2.u1362 = KTree.node A10K2.u1358 (nat_lit 18907757) (nat_lit 5300881204) (nat_lit 0) A10K2.u1361 from rfl, totK_node, atot1358, atot1361]
  decide +kernel

theorem arows1369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1369 = true := by
  rw [show A10K2.u1369 = KTree.node A10K2.u1365 (nat_lit 19009471) (nat_lit 14244862118) (nat_lit 0) A10K2.u1368 from rfl, allE_node, arows1365, irow1369, arows1368]
  all_goals rfl

theorem atot1369 : totK PA10K2 A10K2.u1369 = [0, 0, 1798429062396, 8418192983168, 14155010253816, 10269312004448, 2977207253629, 292982848955, 5546304973, 0] := by
  rw [show A10K2.u1369 = KTree.node A10K2.u1365 (nat_lit 19009471) (nat_lit 14244862118) (nat_lit 0) A10K2.u1368 from rfl, totK_node, atot1365, atot1368]
  decide +kernel

theorem arows1378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1378 = true := by
  rw [show A10K2.u1378 = KTree.node A10K2.u1374 (nat_lit 19054711) (nat_lit 11937418568) (nat_lit 0) A10K2.u1377 from rfl, allE_node, arows1374, irow1378, arows1377]
  all_goals rfl

theorem atot1378 : totK PA10K2 A10K2.u1378 = [0, 0, 994232357131, 6538596675382, 14382794674389, 12091913727628, 3128661731994, 281191347919, 5976421810, 0] := by
  rw [show A10K2.u1378 = KTree.node A10K2.u1374 (nat_lit 19054711) (nat_lit 11937418568) (nat_lit 0) A10K2.u1377 from rfl, totK_node, atot1374, atot1377]
  decide +kernel

theorem arows1385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1385 = true := by
  rw [show A10K2.u1385 = KTree.node A10K2.u1381 (nat_lit 19099524) (nat_lit 7280132914) (nat_lit 0) A10K2.u1384 from rfl, allE_node, arows1381, irow1385, arows1384]
  all_goals rfl

theorem atot1385 : totK PA10K2 A10K2.u1385 = [0, 0, 1311715475833, 7423376524639, 14962024962011, 12182684940032, 3740157281372, 370508635277, 6904928264, 0] := by
  rw [show A10K2.u1385 = KTree.node A10K2.u1381 (nat_lit 19099524) (nat_lit 7280132914) (nat_lit 0) A10K2.u1384 from rfl, totK_node, atot1381, atot1384]
  decide +kernel

theorem arows1393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1393 = true := by
  rw [show A10K2.u1393 = KTree.node A10K2.u1389 (nat_lit 19136865) (nat_lit 9072528644) (nat_lit 0) A10K2.u1392 from rfl, allE_node, arows1389, irow1393, arows1392]
  all_goals rfl

theorem atot1393 : totK PA10K2 A10K2.u1393 = [0, 0, 0, 2785404243214, 11562596978453, 15688259972458, 7744131388437, 1284493150726, 65402222262, 0] := by
  rw [show A10K2.u1393 = KTree.node A10K2.u1389 (nat_lit 19136865) (nat_lit 9072528644) (nat_lit 0) A10K2.u1392 from rfl, totK_node, atot1389, atot1392]
  decide +kernel

theorem arows1400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1400 = true := by
  rw [show A10K2.u1400 = KTree.node A10K2.u1396 (nat_lit 19169207) (nat_lit 15196976937) (nat_lit 0) A10K2.u1399 from rfl, allE_node, arows1396, irow1400, arows1399]
  all_goals rfl

theorem atot1400 : totK PA10K2 A10K2.u1400 = [0, 0, 0, 883603878394, 6169841358528, 13795473058477, 11980972189423, 4303882464911, 646586604106, 30605747850] := by
  rw [show A10K2.u1400 = KTree.node A10K2.u1396 (nat_lit 19169207) (nat_lit 15196976937) (nat_lit 0) A10K2.u1399 from rfl, totK_node, atot1396, atot1399]
  decide +kernel

theorem arows1411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1411 = true := by
  rw [show A10K2.u1411 = KTree.node A10K2.u1407 (nat_lit 19271113) (nat_lit 6782221256) (nat_lit 0) A10K2.u1410 from rfl, allE_node, arows1407, irow1411, arows1410]
  all_goals rfl

theorem atot1411 : totK PA10K2 A10K2.u1411 = [0, 0, 0, 1721849688932, 8318353708474, 14277586472598, 9868964429558, 2749884482368, 267976683222, 5528811039] := by
  rw [show A10K2.u1411 = KTree.node A10K2.u1407 (nat_lit 19271113) (nat_lit 6782221256) (nat_lit 0) A10K2.u1410 from rfl, totK_node, atot1407, atot1410]
  decide +kernel

theorem arows1418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1418 = true := by
  rw [show A10K2.u1418 = KTree.node A10K2.u1414 (nat_lit 19317177) (nat_lit 6698868607) (nat_lit 0) A10K2.u1417 from rfl, allE_node, arows1414, irow1418, arows1417]
  all_goals rfl

theorem atot1418 : totK PA10K2 A10K2.u1418 = [0, 0, 0, 1066246365116, 7052044822471, 14757791209226, 11153872197471, 2859470642197, 273195086918, 5676195732] := by
  rw [show A10K2.u1418 = KTree.node A10K2.u1414 (nat_lit 19317177) (nat_lit 6698868607) (nat_lit 0) A10K2.u1417 from rfl, totK_node, atot1414, atot1417]
  decide +kernel

theorem arows1426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1426 = true := by
  rw [show A10K2.u1426 = KTree.node A10K2.u1422 (nat_lit 19365435) (nat_lit 3451676069) (nat_lit 0) A10K2.u1425 from rfl, allE_node, arows1422, irow1426, arows1425]
  all_goals rfl

theorem atot1426 : totK PA10K2 A10K2.u1426 = [0, 0, 1228511409809, 6459789079719, 13101004072353, 12219671169581, 5375248608906, 917193713931, 50445087986, 0] := by
  rw [show A10K2.u1426 = KTree.node A10K2.u1422 (nat_lit 19365435) (nat_lit 3451676069) (nat_lit 0) A10K2.u1425 from rfl, totK_node, atot1422, atot1425]
  decide +kernel

theorem arows1433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1433 = true := by
  rw [show A10K2.u1433 = KTree.node A10K2.u1429 (nat_lit 19955603) (nat_lit 5102082322) (nat_lit 40) A10K2.u1432 from rfl, allE_node, arows1429, irow1433, arows1432]
  all_goals rfl

theorem atot1433 : totK PA10K2 A10K2.u1433 = [0, 0, 952688695273, 6223423730148, 13778233578290, 12362376063858, 4368621858240, 648593766764, 30650496230, 0] := by
  rw [show A10K2.u1433 = KTree.node A10K2.u1429 (nat_lit 19955603) (nat_lit 5102082322) (nat_lit 40) A10K2.u1432 from rfl, totK_node, atot1429, atot1432]
  decide +kernel

theorem arows1442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1442 = true := by
  rw [show A10K2.u1442 = KTree.node A10K2.u1438 (nat_lit 20002231) (nat_lit 14913432055) (nat_lit 0) A10K2.u1441 from rfl, allE_node, arows1438, irow1442, arows1441]
  all_goals rfl

theorem atot1442 : totK PA10K2 A10K2.u1442 = [0, 0, 1299557310474, 7606180078292, 14855746476027, 11068767326582, 2993364513659, 273301573286, 5546304973, 0] := by
  rw [show A10K2.u1442 = KTree.node A10K2.u1438 (nat_lit 20002231) (nat_lit 14913432055) (nat_lit 0) A10K2.u1441 from rfl, totK_node, atot1438, atot1441]
  decide +kernel

theorem arows1449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1449 = true := by
  rw [show A10K2.u1449 = KTree.node A10K2.u1445 (nat_lit 20058693) (nat_lit 5944113265) (nat_lit 0) A10K2.u1448 from rfl, allE_node, arows1445, irow1449, arows1448]
  all_goals rfl

theorem atot1449 : totK PA10K2 A10K2.u1449 = [0, 0, 1859665716297, 8543503147386, 14390237012866, 10122031647603, 2577949642888, 194351035963, 6121173289, 0] := by
  rw [show A10K2.u1449 = KTree.node A10K2.u1445 (nat_lit 20058693) (nat_lit 5944113265) (nat_lit 0) A10K2.u1448 from rfl, totK_node, atot1445, atot1448]
  decide +kernel

theorem arows1457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1457 = true := by
  rw [show A10K2.u1457 = KTree.node A10K2.u1453 (nat_lit 20097249) (nat_lit 4901734374) (nat_lit 0) A10K2.u1456 from rfl, allE_node, arows1453, irow1457, arows1456]
  all_goals rfl

theorem atot1457 : totK PA10K2 A10K2.u1457 = [0, 0, 308781236982, 4818647290695, 14422556543170, 13747433556493, 3827435900987, 328584891814, 6354482628, 0] := by
  rw [show A10K2.u1457 = KTree.node A10K2.u1453 (nat_lit 20097249) (nat_lit 4901734374) (nat_lit 0) A10K2.u1456 from rfl, totK_node, atot1453, atot1456]
  decide +kernel

theorem arows1464 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1464 = true := by
  rw [show A10K2.u1464 = KTree.node A10K2.u1460 (nat_lit 20206804) (nat_lit 11651063677) (nat_lit 0) A10K2.u1463 from rfl, allE_node, arows1460, irow1464, arows1463]
  all_goals rfl

theorem atot1464 : totK PA10K2 A10K2.u1464 = [0, 0, 0, 2399854211464, 11004794371912, 15997610881077, 7617760119183, 1149391816130, 44026197503, 0] := by
  rw [show A10K2.u1464 = KTree.node A10K2.u1460 (nat_lit 20206804) (nat_lit 11651063677) (nat_lit 0) A10K2.u1463 from rfl, totK_node, atot1460, atot1463]
  decide +kernel

theorem arows1474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1474 = true := by
  rw [show A10K2.u1474 = KTree.node A10K2.u1470 (nat_lit 20321159) (nat_lit 11050397581) (nat_lit 0) A10K2.u1473 from rfl, allE_node, arows1470, irow1474, arows1473]
  all_goals rfl

theorem atot1474 : totK PA10K2 A10K2.u1474 = [0, 0, 0, 2654245219236, 11568841074686, 15648350621540, 6606511376481, 866433515775, 42463581735, 0] := by
  rw [show A10K2.u1474 = KTree.node A10K2.u1470 (nat_lit 20321159) (nat_lit 11050397581) (nat_lit 0) A10K2.u1473 from rfl, totK_node, atot1470, atot1473]
  decide +kernel

theorem arows1481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1481 = true := by
  rw [show A10K2.u1481 = KTree.node A10K2.u1477 (nat_lit 20366624) (nat_lit 10870020494) (nat_lit 0) A10K2.u1480 from rfl, allE_node, arows1477, irow1481, arows1480]
  all_goals rfl

theorem atot1481 : totK PA10K2 A10K2.u1481 = [0, 0, 842261825863, 3390952045022, 7464679898048, 12578094345331, 9882005081112, 2707102324672, 267717460541, 5976421810] := by
  rw [show A10K2.u1481 = KTree.node A10K2.u1477 (nat_lit 20366624) (nat_lit 10870020494) (nat_lit 0) A10K2.u1480 from rfl, totK_node, atot1477, atot1480]
  decide +kernel

theorem arows1489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1489 = true := by
  rw [show A10K2.u1489 = KTree.node A10K2.u1485 (nat_lit 20475379) (nat_lit 8678834121) (nat_lit 0) A10K2.u1488 from rfl, allE_node, arows1485, irow1489, arows1488]
  all_goals rfl

theorem atot1489 : totK PA10K2 A10K2.u1489 = [0, 0, 1367303922230, 7711400029027, 15114315113451, 11493195962279, 3081987963346, 317479712813, 14945844243, 0] := by
  rw [show A10K2.u1489 = KTree.node A10K2.u1485 (nat_lit 20475379) (nat_lit 8678834121) (nat_lit 0) A10K2.u1488 from rfl, totK_node, atot1485, atot1488]
  decide +kernel

theorem arows1496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1496 = true := by
  rw [show A10K2.u1496 = KTree.node A10K2.u1492 (nat_lit 20524423) (nat_lit 14513233492) (nat_lit 0) A10K2.u1495 from rfl, allE_node, arows1492, irow1496, arows1495]
  all_goals rfl

theorem atot1496 : totK PA10K2 A10K2.u1496 = [0, 0, 1688777063667, 8267725246714, 14914916806282, 11600686461161, 3459877048816, 348691798699, 5179162207, 0] := by
  rw [show A10K2.u1496 = KTree.node A10K2.u1492 (nat_lit 20524423) (nat_lit 14513233492) (nat_lit 0) A10K2.u1495 from rfl, totK_node, atot1492, atot1495]
  decide +kernel

theorem arows1505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1505 = true := by
  rw [show A10K2.u1505 = KTree.node A10K2.u1501 (nat_lit 20659269) (nat_lit 3690442997) (nat_lit 0) A10K2.u1504 from rfl, allE_node, arows1501, irow1505, arows1504]
  all_goals rfl

theorem atot1505 : totK PA10K2 A10K2.u1505 = [0, 0, 1981945996222, 9839000870223, 16337638409443, 10016953192879, 1874643178712, 91074288598, 0, 0] := by
  rw [show A10K2.u1505 = KTree.node A10K2.u1501 (nat_lit 20659269) (nat_lit 3690442997) (nat_lit 0) A10K2.u1504 from rfl, totK_node, atot1501, atot1504]
  decide +kernel

theorem arows1512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1512 = true := by
  rw [show A10K2.u1512 = KTree.node A10K2.u1508 (nat_lit 20703125) (nat_lit 3150322667) (nat_lit 32) A10K2.u1511 from rfl, allE_node, arows1508, irow1512, arows1511]
  all_goals rfl

theorem atot1512 : totK PA10K2 A10K2.u1512 = [0, 857716201818, 3393588752070, 6038939531477, 10201791612494, 12336173559312, 6125452170778, 985095467103, 42512946920, 0] := by
  rw [show A10K2.u1512 = KTree.node A10K2.u1508 (nat_lit 20703125) (nat_lit 3150322667) (nat_lit 32) A10K2.u1511 from rfl, totK_node, atot1508, atot1511]
  decide +kernel

theorem arows1520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1520 = true := by
  rw [show A10K2.u1520 = KTree.node A10K2.u1516 (nat_lit 25190856) (nat_lit 14136040694) (nat_lit 0) A10K2.u1519 from rfl, allE_node, arows1516, irow1520, arows1519]
  all_goals rfl

theorem atot1520 : totK PA10K2 A10K2.u1520 = [0, 1435230241487, 8121180038605, 15671353513851, 11296075207693, 2482097108388, 123376106338, 0, 0, 0] := by
  rw [show A10K2.u1520 = KTree.node A10K2.u1516 (nat_lit 25190856) (nat_lit 14136040694) (nat_lit 0) A10K2.u1519 from rfl, totK_node, atot1516, atot1519]
  decide +kernel

theorem arows1527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1527 = true := by
  rw [show A10K2.u1527 = KTree.node A10K2.u1523 (nat_lit 25223274) (nat_lit 3134791679) (nat_lit 0) A10K2.u1526 from rfl, allE_node, arows1523, irow1527, arows1526]
  all_goals rfl

theorem atot1527 : totK PA10K2 A10K2.u1527 = [0, 786880231059, 4986708980987, 12287278925058, 13592095781043, 5908392849555, 867160478426, 36196801203, 0, 0] := by
  rw [show A10K2.u1527 = KTree.node A10K2.u1523 (nat_lit 25223274) (nat_lit 3134791679) (nat_lit 0) A10K2.u1526 from rfl, totK_node, atot1523, atot1526]
  decide +kernel

theorem arows1540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1540 = true := by
  rw [show A10K2.u1540 = KTree.node A10K2.u1536 (nat_lit 25317640) (nat_lit 13973501234) (nat_lit 0) A10K2.u1539 from rfl, allE_node, arows1536, irow1540, arows1539]
  all_goals rfl

theorem atot1540 : totK PA10K2 A10K2.u1540 = [0, 1328023409878, 7821982910304, 15259060628552, 10920155236226, 2337776982417, 128691162287, 0, 0, 0] := by
  rw [show A10K2.u1540 = KTree.node A10K2.u1536 (nat_lit 25317640) (nat_lit 13973501234) (nat_lit 0) A10K2.u1539 from rfl, totK_node, atot1536, atot1539]
  decide +kernel

theorem arows1547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1547 = true := by
  rw [show A10K2.u1547 = KTree.node A10K2.u1543 (nat_lit 25366790) (nat_lit 11657215689) (nat_lit 0) A10K2.u1546 from rfl, allE_node, arows1543, irow1547, arows1546]
  all_goals rfl

theorem atot1547 : totK PA10K2 A10K2.u1547 = [0, 1605739312950, 8022448920336, 14686731926496, 11410693535839, 3285150255070, 340283906111, 6354482628, 0, 0] := by
  rw [show A10K2.u1547 = KTree.node A10K2.u1543 (nat_lit 25366790) (nat_lit 11657215689) (nat_lit 0) A10K2.u1546 from rfl, totK_node, atot1543, atot1546]
  decide +kernel

theorem arows1555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1555 = true := by
  rw [show A10K2.u1555 = KTree.node A10K2.u1551 (nat_lit 25423358) (nat_lit 15941591276) (nat_lit 0) A10K2.u1554 from rfl, allE_node, arows1551, irow1555, arows1554]
  all_goals rfl

theorem atot1555 : totK PA10K2 A10K2.u1555 = [0, 0, 2459964362670, 10932818302435, 16222740737503, 8692686431002, 1457378352971, 67884127913, 0, 0] := by
  rw [show A10K2.u1555 = KTree.node A10K2.u1551 (nat_lit 25423358) (nat_lit 15941591276) (nat_lit 0) A10K2.u1554 from rfl, totK_node, atot1551, atot1554]
  decide +kernel

theorem arows1562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1562 = true := by
  rw [show A10K2.u1562 = KTree.node A10K2.u1558 (nat_lit 25454526) (nat_lit 16179429963) (nat_lit 0) A10K2.u1561 from rfl, allE_node, arows1558, irow1562, arows1561]
  all_goals rfl

theorem atot1562 : totK PA10K2 A10K2.u1562 = [0, 0, 1433613286411, 8041154157025, 15195741460910, 10855470631562, 2795525578905, 330929905098, 20060612110, 0] := by
  rw [show A10K2.u1562 = KTree.node A10K2.u1558 (nat_lit 25454526) (nat_lit 16179429963) (nat_lit 0) A10K2.u1561 from rfl, totK_node, atot1558, atot1561]
  decide +kernel

theorem arows1571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1571 = true := by
  rw [show A10K2.u1571 = KTree.node A10K2.u1567 (nat_lit 25488560) (nat_lit 11782787034) (nat_lit 0) A10K2.u1570 from rfl, allE_node, arows1567, irow1571, arows1570]
  all_goals rfl

theorem atot1571 : totK PA10K2 A10K2.u1571 = [0, 0, 1196895285670, 6344870808860, 13200163178901, 12201960889514, 4476279987728, 588565493142, 16073946779, 0] := by
  rw [show A10K2.u1571 = KTree.node A10K2.u1567 (nat_lit 25488560) (nat_lit 11782787034) (nat_lit 0) A10K2.u1570 from rfl, totK_node, atot1567, atot1570]
  decide +kernel

theorem arows1578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1578 = true := by
  rw [show A10K2.u1578 = KTree.node A10K2.u1574 (nat_lit 25591885) (nat_lit 5556177515) (nat_lit 0) A10K2.u1577 from rfl, allE_node, arows1574, irow1578, arows1577]
  all_goals rfl

theorem atot1578 : totK PA10K2 A10K2.u1578 = [0, 0, 916882235497, 6961192795959, 15453880883680, 11386056715835, 2409786208227, 119945278399, 0, 0] := by
  rw [show A10K2.u1578 = KTree.node A10K2.u1574 (nat_lit 25591885) (nat_lit 5556177515) (nat_lit 0) A10K2.u1577 from rfl, totK_node, atot1574, atot1577]
  decide +kernel

theorem arows1586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1586 = true := by
  rw [show A10K2.u1586 = KTree.node A10K2.u1582 (nat_lit 25650361) (nat_lit 5306908948) (nat_lit 0) A10K2.u1585 from rfl, allE_node, arows1582, irow1586, arows1585]
  all_goals rfl

theorem atot1586 : totK PA10K2 A10K2.u1586 = [0, 843291061595, 4690722113576, 10752236458181, 13051884074838, 8012932284122, 2145273054849, 222016331383, 5676195732, 0] := by
  rw [show A10K2.u1586 = KTree.node A10K2.u1582 (nat_lit 25650361) (nat_lit 5306908948) (nat_lit 0) A10K2.u1585 from rfl, totK_node, atot1582, atot1585]
  decide +kernel

theorem arows1593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1593 = true := by
  rw [show A10K2.u1593 = KTree.node A10K2.u1589 (nat_lit 25779013) (nat_lit 6792366345) (nat_lit 0) A10K2.u1592 from rfl, allE_node, arows1589, irow1593, arows1592]
  all_goals rfl

theorem atot1593 : totK PA10K2 A10K2.u1593 = [0, 1342370522690, 7924977922648, 15687013206923, 11423358099688, 2519639147308, 120390938583, 0, 0, 0] := by
  rw [show A10K2.u1593 = KTree.node A10K2.u1589 (nat_lit 25779013) (nat_lit 6792366345) (nat_lit 0) A10K2.u1592 from rfl, totK_node, atot1589, atot1592]
  decide +kernel

theorem arows1603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1603 = true := by
  rw [show A10K2.u1603 = KTree.node A10K2.u1599 (nat_lit 25814202) (nat_lit 15041214133) (nat_lit 0) A10K2.u1602 from rfl, allE_node, arows1599, irow1603, arows1602]
  all_goals rfl

theorem atot1603 : totK PA10K2 A10K2.u1603 = [0, 929693221955, 5215839303096, 11929695183445, 13187134798471, 6013832110168, 905883551663, 37204059898, 0, 0] := by
  rw [show A10K2.u1603 = KTree.node A10K2.u1599 (nat_lit 25814202) (nat_lit 15041214133) (nat_lit 0) A10K2.u1602 from rfl, totK_node, atot1599, atot1602]
  decide +kernel

theorem arows1610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1610 = true := by
  rw [show A10K2.u1610 = KTree.node A10K2.u1606 (nat_lit 25841946) (nat_lit 12515433906) (nat_lit 0) A10K2.u1609 from rfl, allE_node, arows1606, irow1610, arows1609]
  all_goals rfl

theorem atot1610 : totK PA10K2 A10K2.u1610 = [0, 1219255596760, 7652602176721, 15508600145621, 11375144839785, 2451176520350, 128769187112, 0, 0, 0] := by
  rw [show A10K2.u1610 = KTree.node A10K2.u1606 (nat_lit 25841946) (nat_lit 12515433906) (nat_lit 0) A10K2.u1609 from rfl, totK_node, atot1606, atot1609]
  decide +kernel

theorem arows1618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1618 = true := by
  rw [show A10K2.u1618 = KTree.node A10K2.u1614 (nat_lit 26031265) (nat_lit 5446225659) (nat_lit 0) A10K2.u1617 from rfl, allE_node, arows1614, irow1618, arows1617]
  all_goals rfl

theorem atot1618 : totK PA10K2 A10K2.u1618 = [0, 0, 2318744367512, 10642547858451, 15868220550848, 7849555247685, 1179270912285, 44362905215, 0, 0] := by
  rw [show A10K2.u1618 = KTree.node A10K2.u1614 (nat_lit 26031265) (nat_lit 5446225659) (nat_lit 0) A10K2.u1617 from rfl, totK_node, atot1614, atot1617]
  decide +kernel

theorem arows1625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1625 = true := by
  rw [show A10K2.u1625 = KTree.node A10K2.u1621 (nat_lit 26092896) (nat_lit 9729420434) (nat_lit 0) A10K2.u1624 from rfl, allE_node, arows1621, irow1625, arows1624]
  all_goals rfl

theorem atot1625 : totK PA10K2 A10K2.u1625 = [0, 0, 2588935317114, 11217386031399, 15992507213306, 7890938815630, 1138525375162, 44191984097, 0, 0] := by
  rw [show A10K2.u1625 = KTree.node A10K2.u1621 (nat_lit 26092896) (nat_lit 9729420434) (nat_lit 0) A10K2.u1624 from rfl, totK_node, atot1621, atot1624]
  decide +kernel

theorem arows1634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1634 = true := by
  rw [show A10K2.u1634 = KTree.node A10K2.u1630 (nat_lit 26133032) (nat_lit 12564771568) (nat_lit 0) A10K2.u1633 from rfl, allE_node, arows1630, irow1634, arows1633]
  all_goals rfl

theorem atot1634 : totK PA10K2 A10K2.u1634 = [0, 812666997328, 3078376079659, 6720417911770, 12444829686378, 11109976185253, 3086434274184, 295822231090, 6239673734, 0] := by
  rw [show A10K2.u1634 = KTree.node A10K2.u1630 (nat_lit 26133032) (nat_lit 12564771568) (nat_lit 0) A10K2.u1633 from rfl, totK_node, atot1630, atot1633]
  decide +kernel

theorem arows1641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1641 = true := by
  rw [show A10K2.u1641 = KTree.node A10K2.u1637 (nat_lit 26239046) (nat_lit 14943008976) (nat_lit 0) A10K2.u1640 from rfl, allE_node, arows1637, irow1641, arows1640]
  all_goals rfl

theorem atot1641 : totK PA10K2 A10K2.u1641 = [0, 1281297638069, 7448822784902, 14911650297894, 11528113901953, 3169600045830, 353019182517, 20060612110, 0, 0] := by
  rw [show A10K2.u1641 = KTree.node A10K2.u1637 (nat_lit 26239046) (nat_lit 14943008976) (nat_lit 0) A10K2.u1640 from rfl, totK_node, atot1637, atot1640]
  decide +kernel

theorem arows1649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1649 = true := by
  rw [show A10K2.u1649 = KTree.node A10K2.u1645 (nat_lit 26275213) (nat_lit 3528066320) (nat_lit 0) A10K2.u1648 from rfl, allE_node, arows1645, irow1649, arows1648]
  all_goals rfl

theorem atot1649 : totK PA10K2 A10K2.u1649 = [0, 1246455274452, 6387510763137, 12898295647157, 12404194694195, 4819987591091, 615118386240, 16136189093, 0, 0] := by
  rw [show A10K2.u1649 = KTree.node A10K2.u1645 (nat_lit 26275213) (nat_lit 3528066320) (nat_lit 0) A10K2.u1648 from rfl, totK_node, atot1645, atot1648]
  decide +kernel

theorem arows1656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1656 = true := by
  rw [show A10K2.u1656 = KTree.node A10K2.u1652 (nat_lit 26323780) (nat_lit 12549093348) (nat_lit 0) A10K2.u1655 from rfl, allE_node, arows1652, irow1656, arows1655]
  all_goals rfl

theorem atot1656 : totK PA10K2 A10K2.u1656 = [0, 566126593814, 4853569698486, 13127405515635, 13761303238577, 5139797307374, 624821591620, 31082886609, 0, 0] := by
  rw [show A10K2.u1656 = KTree.node A10K2.u1652 (nat_lit 26323780) (nat_lit 12549093348) (nat_lit 0) A10K2.u1655 from rfl, totK_node, atot1652, atot1655]
  decide +kernel

theorem arows1667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1667 = true := by
  rw [show A10K2.u1667 = KTree.node A10K2.u1663 (nat_lit 26355428) (nat_lit 12617738209) (nat_lit 0) A10K2.u1666 from rfl, allE_node, arows1663, irow1667, arows1666]
  all_goals rfl

theorem atot1667 : totK PA10K2 A10K2.u1667 = [0, 2296331471068, 10068414485895, 14768929074175, 8472604332133, 2048658260899, 224061185607, 6121173289, 0, 0] := by
  rw [show A10K2.u1667 = KTree.node A10K2.u1663 (nat_lit 26355428) (nat_lit 12617738209) (nat_lit 0) A10K2.u1666 from rfl, totK_node, atot1663, atot1666]
  decide +kernel

theorem arows1674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1674 = true := by
  rw [show A10K2.u1674 = KTree.node A10K2.u1670 (nat_lit 26390228) (nat_lit 9389257169) (nat_lit 0) A10K2.u1673 from rfl, allE_node, arows1670, irow1674, arows1673]
  all_goals rfl

theorem atot1674 : totK PA10K2 A10K2.u1674 = [0, 0, 3803051488763, 13888382532777, 14954876665060, 4621461681950, 432563266740, 6354482628, 0, 0] := by
  rw [show A10K2.u1674 = KTree.node A10K2.u1670 (nat_lit 26390228) (nat_lit 9389257169) (nat_lit 0) A10K2.u1673 from rfl, totK_node, atot1670, atot1673]
  decide +kernel

theorem arows1682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1682 = true := by
  rw [show A10K2.u1682 = KTree.node A10K2.u1678 (nat_lit 26499144) (nat_lit 12191444535) (nat_lit 0) A10K2.u1681 from rfl, allE_node, arows1678, irow1682, arows1681]
  all_goals rfl

theorem atot1682 : totK PA10K2 A10K2.u1682 = [0, 0, 2182823910686, 10463442263237, 16195341573995, 8515871984156, 1274281993031, 44026197503, 0, 0] := by
  rw [show A10K2.u1682 = KTree.node A10K2.u1678 (nat_lit 26499144) (nat_lit 12191444535) (nat_lit 0) A10K2.u1681 from rfl, totK_node, atot1678, atot1681]
  decide +kernel

theorem arows1689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1689 = true := by
  rw [show A10K2.u1689 = KTree.node A10K2.u1685 (nat_lit 26568349) (nat_lit 5905229378) (nat_lit 0) A10K2.u1688 from rfl, allE_node, arows1685, irow1689, arows1688]
  all_goals rfl

theorem atot1689 : totK PA10K2 A10K2.u1689 = [0, 0, 2188725545613, 10139098387433, 15693926497872, 8398819048257, 1345481912146, 67881940024, 0, 0] := by
  rw [show A10K2.u1689 = KTree.node A10K2.u1685 (nat_lit 26568349) (nat_lit 5905229378) (nat_lit 0) A10K2.u1688 from rfl, totK_node, atot1685, atot1688]
  decide +kernel

theorem arows1698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1698 = true := by
  rw [show A10K2.u1698 = KTree.node A10K2.u1694 (nat_lit 26629303) (nat_lit 10937772665) (nat_lit 0) A10K2.u1697 from rfl, allE_node, arows1694, irow1698, arows1697]
  all_goals rfl

theorem atot1698 : totK PA10K2 A10K2.u1698 = [0, 0, 1140595278057, 7668744788583, 15528792168036, 10472327136019, 2146292463328, 124897332203, 0, 0] := by
  rw [show A10K2.u1698 = KTree.node A10K2.u1694 (nat_lit 26629303) (nat_lit 10937772665) (nat_lit 0) A10K2.u1697 from rfl, totK_node, atot1694, atot1697]
  decide +kernel

theorem arows1705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1705 = true := by
  rw [show A10K2.u1705 = KTree.node A10K2.u1701 (nat_lit 27267424) (nat_lit 12824100409) (nat_lit 0) A10K2.u1704 from rfl, allE_node, arows1701, irow1705, arows1704]
  all_goals rfl

theorem atot1705 : totK PA10K2 A10K2.u1705 = [0, 0, 1894444922203, 8516872075504, 14132641919214, 9940478963436, 2821940168125, 328254832860, 6354482628, 0] := by
  rw [show A10K2.u1705 = KTree.node A10K2.u1701 (nat_lit 27267424) (nat_lit 12824100409) (nat_lit 0) A10K2.u1704 from rfl, totK_node, atot1701, atot1704]
  decide +kernel

theorem arows1713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1713 = true := by
  rw [show A10K2.u1713 = KTree.node A10K2.u1709 (nat_lit 27299771) (nat_lit 4387552982) (nat_lit 8) A10K2.u1712 from rfl, allE_node, arows1709, irow1713, arows1712]
  all_goals rfl

theorem atot1713 : totK PA10K2 A10K2.u1713 = [0, 0, 395296435550, 4346716320676, 12841711473136, 14421948480927, 5785899539573, 847096795511, 36196801203, 0] := by
  rw [show A10K2.u1713 = KTree.node A10K2.u1709 (nat_lit 27299771) (nat_lit 4387552982) (nat_lit 8) A10K2.u1712 from rfl, totK_node, atot1709, atot1712]
  decide +kernel

theorem arows1720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1720 = true := by
  rw [show A10K2.u1720 = KTree.node A10K2.u1716 (nat_lit 27403426) (nat_lit 14523975480) (nat_lit 0) A10K2.u1719 from rfl, allE_node, arows1716, irow1720, arows1719]
  all_goals rfl

theorem atot1720 : totK PA10K2 A10K2.u1720 = [0, 0, 2105630273716, 9888168694441, 15580628124246, 9110784599110, 1705921896857, 92146351067, 0, 0] := by
  rw [show A10K2.u1720 = KTree.node A10K2.u1716 (nat_lit 27403426) (nat_lit 14523975480) (nat_lit 0) A10K2.u1719 from rfl, totK_node, atot1716, atot1719]
  decide +kernel

theorem arows1730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1730 = true := by
  rw [show A10K2.u1730 = KTree.node A10K2.u1726 (nat_lit 27445056) (nat_lit 11719544828) (nat_lit 0) A10K2.u1729 from rfl, allE_node, arows1726, irow1730, arows1729]
  all_goals rfl

theorem atot1730 : totK PA10K2 A10K2.u1730 = [0, 0, 808480932972, 5857358614734, 14228047691727, 13115908942308, 3756725722426, 328250108612, 6354482628, 0] := by
  rw [show A10K2.u1730 = KTree.node A10K2.u1726 (nat_lit 27445056) (nat_lit 11719544828) (nat_lit 0) A10K2.u1729 from rfl, totK_node, atot1726, atot1729]
  decide +kernel

theorem arows1737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1737 = true := by
  rw [show A10K2.u1737 = KTree.node A10K2.u1733 (nat_lit 27493218) (nat_lit 6618223050) (nat_lit 0) A10K2.u1736 from rfl, allE_node, arows1733, irow1737, arows1736]
  all_goals rfl

theorem atot1737 : totK PA10K2 A10K2.u1737 = [0, 0, 1211760767946, 7024400195226, 14860154257465, 12841231319067, 4011723326425, 405524309157, 6904928264, 0] := by
  rw [show A10K2.u1737 = KTree.node A10K2.u1733 (nat_lit 27493218) (nat_lit 6618223050) (nat_lit 0) A10K2.u1736 from rfl, totK_node, atot1733, atot1736]
  decide +kernel

theorem arows1745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1745 = true := by
  rw [show A10K2.u1745 = KTree.node A10K2.u1741 (nat_lit 27873636) (nat_lit 13775768551) (nat_lit 0) A10K2.u1744 from rfl, allE_node, arows1741, irow1745, arows1744]
  all_goals rfl

theorem atot1745 : totK PA10K2 A10K2.u1745 = [0, 0, 2326891837919, 10612887048808, 15973931722617, 8677972586941, 1410688329913, 51049352985, 0, 0] := by
  rw [show A10K2.u1745 = KTree.node A10K2.u1741 (nat_lit 27873636) (nat_lit 13775768551) (nat_lit 0) A10K2.u1744 from rfl, totK_node, atot1741, atot1744]
  decide +kernel

theorem arows1752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1752 = true := by
  rw [show A10K2.u1752 = KTree.node A10K2.u1748 (nat_lit 27934195) (nat_lit 8868770518) (nat_lit 0) A10K2.u1751 from rfl, allE_node, arows1748, irow1752, arows1751]
  all_goals rfl

theorem atot1752 : totK PA10K2 A10K2.u1752 = [0, 0, 1585922971270, 8781490060678, 15911415647119, 9987252893792, 1682224583654, 65897278882, 0, 0] := by
  rw [show A10K2.u1752 = KTree.node A10K2.u1748 (nat_lit 27934195) (nat_lit 8868770518) (nat_lit 0) A10K2.u1751 from rfl, totK_node, atot1748, atot1751]
  decide +kernel

theorem arows1761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1761 = true := by
  rw [show A10K2.u1761 = KTree.node A10K2.u1757 (nat_lit 28311845) (nat_lit 7314703828) (nat_lit 0) A10K2.u1760 from rfl, allE_node, arows1757, irow1761, arows1760]
  all_goals rfl

theorem atot1761 : totK PA10K2 A10K2.u1761 = [0, 0, 1437738826139, 7302475055018, 13973653990152, 11415953497635, 3280998357486, 329493328679, 6354482628, 0] := by
  rw [show A10K2.u1761 = KTree.node A10K2.u1757 (nat_lit 28311845) (nat_lit 7314703828) (nat_lit 0) A10K2.u1760 from rfl, totK_node, atot1757, atot1760]
  decide +kernel

theorem arows1768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1768 = true := by
  rw [show A10K2.u1768 = KTree.node A10K2.u1764 (nat_lit 28346433) (nat_lit 10335345372) (nat_lit 0) A10K2.u1767 from rfl, allE_node, arows1764, irow1768, arows1767]
  all_goals rfl

theorem atot1768 : totK PA10K2 A10K2.u1768 = [0, 0, 636947652353, 5427345505966, 13895873981331, 13374600381650, 4407312108555, 563559159074, 30220878370, 0] := by
  rw [show A10K2.u1768 = KTree.node A10K2.u1764 (nat_lit 28346433) (nat_lit 10335345372) (nat_lit 0) A10K2.u1767 from rfl, totK_node, atot1764, atot1767]
  decide +kernel

theorem arows1776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1776 = true := by
  rw [show A10K2.u1776 = KTree.node A10K2.u1772 (nat_lit 28392220) (nat_lit 11922857172) (nat_lit 0) A10K2.u1775 from rfl, allE_node, arows1772, irow1776, arows1775]
  all_goals rfl

theorem atot1776 : totK PA10K2 A10K2.u1776 = [0, 0, 1811215867801, 8948762023978, 15119638594751, 10111254895845, 2462697525409, 239856464887, 5546304973, 0] := by
  rw [show A10K2.u1776 = KTree.node A10K2.u1772 (nat_lit 28392220) (nat_lit 11922857172) (nat_lit 0) A10K2.u1775 from rfl, totK_node, atot1772, atot1775]
  decide +kernel

theorem arows1783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1783 = true := by
  rw [show A10K2.u1783 = KTree.node A10K2.u1779 (nat_lit 28443490) (nat_lit 8875718346) (nat_lit 0) A10K2.u1782 from rfl, allE_node, arows1779, irow1783, arows1782]
  all_goals rfl

theorem atot1783 : totK PA10K2 A10K2.u1783 = [0, 0, 1440160451792, 7727205606681, 14569790884026, 11022497195038, 2939511661078, 287296933972, 6121173289, 0] := by
  rw [show A10K2.u1783 = KTree.node A10K2.u1779 (nat_lit 28443490) (nat_lit 8875718346) (nat_lit 0) A10K2.u1782 from rfl, totK_node, atot1779, atot1782]
  decide +kernel

theorem arows1795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1795 = true := by
  rw [show A10K2.u1795 = KTree.node A10K2.u1791 (nat_lit 28475835) (nat_lit 1478729551) (nat_lit 0) A10K2.u1794 from rfl, allE_node, arows1791, irow1795, arows1794]
  all_goals rfl

theorem atot1795 : totK PA10K2 A10K2.u1795 = [0, 0, 845557281498, 6604291146478, 15300564051216, 12122812921638, 2641661096942, 159213676587, 0, 0] := by
  rw [show A10K2.u1795 = KTree.node A10K2.u1791 (nat_lit 28475835) (nat_lit 1478729551) (nat_lit 0) A10K2.u1794 from rfl, totK_node, atot1791, atot1794]
  decide +kernel

theorem arows1802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1802 = true := by
  rw [show A10K2.u1802 = KTree.node A10K2.u1798 (nat_lit 28580964) (nat_lit 11478852723) (nat_lit 0) A10K2.u1801 from rfl, allE_node, arows1798, irow1802, arows1801]
  all_goals rfl

theorem atot1802 : totK PA10K2 A10K2.u1802 = [0, 0, 0, 2385355590564, 11045014510108, 16038786772435, 7299790197155, 1057743695739, 43097714263, 0] := by
  rw [show A10K2.u1802 = KTree.node A10K2.u1798 (nat_lit 28580964) (nat_lit 11478852723) (nat_lit 0) A10K2.u1801 from rfl, totK_node, atot1798, atot1801]
  decide +kernel

theorem arows1810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1810 = true := by
  rw [show A10K2.u1810 = KTree.node A10K2.u1806 (nat_lit 28705060) (nat_lit 13732563620) (nat_lit 0) A10K2.u1809 from rfl, allE_node, arows1806, irow1810, arows1809]
  all_goals rfl

theorem atot1810 : totK PA10K2 A10K2.u1810 = [0, 0, 0, 2935216609442, 12187672629917, 15668007824865, 6181475772769, 859086741855, 36429366174, 0] := by
  rw [show A10K2.u1810 = KTree.node A10K2.u1806 (nat_lit 28705060) (nat_lit 13732563620) (nat_lit 0) A10K2.u1809 from rfl, totK_node, atot1806, atot1809]
  decide +kernel

theorem arows1817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1817 = true := by
  rw [show A10K2.u1817 = KTree.node A10K2.u1813 (nat_lit 28739742) (nat_lit 3050826347) (nat_lit 8) A10K2.u1816 from rfl, allE_node, arows1813, irow1817, arows1816]
  all_goals rfl

theorem atot1817 : totK PA10K2 A10K2.u1817 = [0, 157526836586, 329480614415, 1024869892313, 6452301532182, 14536943660422, 11135357826830, 3067795413651, 275877751381, 6354482628] := by
  rw [show A10K2.u1817 = KTree.node A10K2.u1813 (nat_lit 28739742) (nat_lit 3050826347) (nat_lit 8) A10K2.u1816 from rfl, totK_node, atot1813, atot1816]
  decide +kernel

theorem arows1826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1826 = true := by
  rw [show A10K2.u1826 = KTree.node A10K2.u1822 (nat_lit 29378830) (nat_lit 8531122299) (nat_lit 0) A10K2.u1825 from rfl, allE_node, arows1822, irow1826, arows1825]
  all_goals rfl

theorem atot1826 : totK PA10K2 A10K2.u1826 = [0, 2142876281003, 10353986011446, 16189662128088, 8867002614987, 1451334884862, 50989814142, 0, 0, 0] := by
  rw [show A10K2.u1826 = KTree.node A10K2.u1822 (nat_lit 29378830) (nat_lit 8531122299) (nat_lit 0) A10K2.u1825 from rfl, totK_node, atot1822, atot1825]
  decide +kernel

theorem arows1833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1833 = true := by
  rw [show A10K2.u1833 = KTree.node A10K2.u1829 (nat_lit 29410183) (nat_lit 13745903249) (nat_lit 0) A10K2.u1832 from rfl, allE_node, arows1829, irow1833, arows1832]
  all_goals rfl

theorem atot1833 : totK PA10K2 A10K2.u1833 = [0, 506452765222, 3905418191411, 11775474133376, 14852250382543, 6599966026288, 938407442871, 36196801203, 0, 0] := by
  rw [show A10K2.u1833 = KTree.node A10K2.u1829 (nat_lit 29410183) (nat_lit 13745903249) (nat_lit 0) A10K2.u1832 from rfl, totK_node, atot1829, atot1832]
  decide +kernel

theorem arows1841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1841 = true := by
  rw [show A10K2.u1841 = KTree.node A10K2.u1837 (nat_lit 29513066) (nat_lit 9940403154) (nat_lit 0) A10K2.u1840 from rfl, allE_node, arows1837, irow1841, arows1840]
  all_goals rfl

theorem atot1841 : totK PA10K2 A10K2.u1841 = [0, 1016920628206, 7027366932000, 15330436518020, 12102549474841, 2834788731368, 164542016753, 0, 0, 0] := by
  rw [show A10K2.u1841 = KTree.node A10K2.u1837 (nat_lit 29513066) (nat_lit 9940403154) (nat_lit 0) A10K2.u1840 from rfl, totK_node, atot1837, atot1840]
  decide +kernel

theorem arows1848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1848 = true := by
  rw [show A10K2.u1848 = KTree.node A10K2.u1844 (nat_lit 29568392) (nat_lit 13346482372) (nat_lit 0) A10K2.u1847 from rfl, allE_node, arows1844, irow1848, arows1847]
  all_goals rfl

theorem atot1848 : totK PA10K2 A10K2.u1848 = [0, 2222037618697, 10047997533310, 15492872515379, 9380034915690, 2181865697869, 195713812580, 6354482628, 0, 0] := by
  rw [show A10K2.u1848 = KTree.node A10K2.u1844 (nat_lit 29568392) (nat_lit 13346482372) (nat_lit 0) A10K2.u1847 from rfl, totK_node, atot1844, atot1847]
  decide +kernel

theorem arows1858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1858 = true := by
  rw [show A10K2.u1858 = KTree.node A10K2.u1854 (nat_lit 29600825) (nat_lit 7011011615) (nat_lit 0) A10K2.u1857 from rfl, allE_node, arows1854, irow1858, arows1857]
  all_goals rfl

theorem atot1858 : totK PA10K2 A10K2.u1858 = [0, 0, 2546544878875, 11312418107004, 16499244067550, 8293244998619, 1047117443700, 20018912194, 0, 0] := by
  rw [show A10K2.u1858 = KTree.node A10K2.u1854 (nat_lit 29600825) (nat_lit 7011011615) (nat_lit 0) A10K2.u1857 from rfl, totK_node, atot1854, atot1857]
  decide +kernel

theorem arows1865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1865 = true := by
  rw [show A10K2.u1865 = KTree.node A10K2.u1861 (nat_lit 29638661) (nat_lit 6691629675) (nat_lit 0) A10K2.u1864 from rfl, allE_node, arows1861, irow1865, arows1864]
  all_goals rfl

theorem atot1865 : totK PA10K2 A10K2.u1865 = [0, 0, 2300403117589, 10439200121781, 15726470458775, 8562668708476, 1619729540643, 91579861429, 0, 0] := by
  rw [show A10K2.u1865 = KTree.node A10K2.u1861 (nat_lit 29638661) (nat_lit 6691629675) (nat_lit 0) A10K2.u1864 from rfl, totK_node, atot1861, atot1864]
  decide +kernel

theorem arows1873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1873 = true := by
  rw [show A10K2.u1873 = KTree.node A10K2.u1869 (nat_lit 29662597) (nat_lit 4441337984) (nat_lit 0) A10K2.u1872 from rfl, allE_node, arows1869, irow1873, arows1872]
  all_goals rfl

theorem atot1873 : totK PA10K2 A10K2.u1873 = [0, 0, 307513935741, 3871389826277, 12516200838271, 14743271270115, 6052009914649, 877088968968, 36134558889, 0] := by
  rw [show A10K2.u1873 = KTree.node A10K2.u1869 (nat_lit 29662597) (nat_lit 4441337984) (nat_lit 0) A10K2.u1872 from rfl, totK_node, atot1869, atot1872]
  decide +kernel

theorem arows1880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1880 = true := by
  rw [show A10K2.u1880 = KTree.node A10K2.u1876 (nat_lit 29774209) (nat_lit 10262273138) (nat_lit 0) A10K2.u1879 from rfl, allE_node, arows1876, irow1880, arows1879]
  all_goals rfl

theorem atot1880 : totK PA10K2 A10K2.u1880 = [0, 0, 2282125118620, 10691248729024, 16160958153897, 8299493742333, 1324398799231, 62499504683, 0, 0] := by
  rw [show A10K2.u1880 = KTree.node A10K2.u1876 (nat_lit 29774209) (nat_lit 10262273138) (nat_lit 0) A10K2.u1879 from rfl, totK_node, atot1876, atot1879]
  decide +kernel

theorem arows1889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1889 = true := by
  rw [show A10K2.u1889 = KTree.node A10K2.u1885 (nat_lit 29849046) (nat_lit 15723628633) (nat_lit 0) A10K2.u1888 from rfl, allE_node, arows1885, irow1889, arows1888]
  all_goals rfl

theorem atot1889 : totK PA10K2 A10K2.u1889 = [0, 847358390021, 5112700333913, 11838394707795, 13327013513772, 7074533336906, 1372919259597, 69519743899, 0, 0] := by
  rw [show A10K2.u1889 = KTree.node A10K2.u1885 (nat_lit 29849046) (nat_lit 15723628633) (nat_lit 0) A10K2.u1888 from rfl, totK_node, atot1885, atot1888]
  decide +kernel

theorem arows1896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1896 = true := by
  rw [show A10K2.u1896 = KTree.node A10K2.u1892 (nat_lit 29979870) (nat_lit 11389925001) (nat_lit 0) A10K2.u1895 from rfl, allE_node, arows1892, irow1896, arows1895]
  all_goals rfl

theorem atot1896 : totK PA10K2 A10K2.u1896 = [0, 1363868382074, 7202751945278, 13959855023170, 11802896905464, 4302584990162, 634652286298, 31082886609, 0, 0] := by
  rw [show A10K2.u1896 = KTree.node A10K2.u1892 (nat_lit 29979870) (nat_lit 11389925001) (nat_lit 0) A10K2.u1895 from rfl, totK_node, atot1892, atot1895]
  decide +kernel

theorem arows1904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1904 = true := by
  rw [show A10K2.u1904 = KTree.node A10K2.u1900 (nat_lit 30081540) (nat_lit 11565767774) (nat_lit 0) A10K2.u1903 from rfl, allE_node, arows1900, irow1904, arows1903]
  all_goals rfl

theorem atot1904 : totK PA10K2 A10K2.u1904 = [0, 1379554642640, 7361326687217, 14380968497972, 12164838579485, 4010719524612, 383944197824, 6121173289, 0, 0] := by
  rw [show A10K2.u1904 = KTree.node A10K2.u1900 (nat_lit 30081540) (nat_lit 11565767774) (nat_lit 0) A10K2.u1903 from rfl, totK_node, atot1900, atot1903]
  decide +kernel

theorem arows1911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1911 = true := by
  rw [show A10K2.u1911 = KTree.node A10K2.u1907 (nat_lit 30113678) (nat_lit 15054305658) (nat_lit 0) A10K2.u1910 from rfl, allE_node, arows1907, irow1911, arows1910]
  all_goals rfl

theorem atot1911 : totK PA10K2 A10K2.u1911 = [0, 866947050573, 5867860517620, 14038447580197, 13786307984920, 4946707319616, 472725132467, 6904928264, 0, 0] := by
  rw [show A10K2.u1911 = KTree.node A10K2.u1907 (nat_lit 30113678) (nat_lit 15054305658) (nat_lit 0) A10K2.u1910 from rfl, totK_node, atot1907, atot1910]
  decide +kernel

theorem arows1922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1922 = true := by
  rw [show A10K2.u1922 = KTree.node A10K2.u1918 (nat_lit 30146231) (nat_lit 14854120808) (nat_lit 0) A10K2.u1921 from rfl, allE_node, arows1918, irow1922, arows1921]
  all_goals rfl

theorem atot1922 : totK PA10K2 A10K2.u1922 = [0, 0, 2116166840260, 9795771450218, 15695042993886, 9731424955562, 1918352335236, 99925900411, 0, 0] := by
  rw [show A10K2.u1922 = KTree.node A10K2.u1918 (nat_lit 30146231) (nat_lit 14854120808) (nat_lit 0) A10K2.u1921 from rfl, totK_node, atot1918, atot1921]
  decide +kernel

theorem arows1929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1929 = true := by
  rw [show A10K2.u1929 = KTree.node A10K2.u1925 (nat_lit 30244360) (nat_lit 12779158875) (nat_lit 0) A10K2.u1928 from rfl, allE_node, arows1925, irow1929, arows1928]
  all_goals rfl

theorem atot1929 : totK PA10K2 A10K2.u1929 = [0, 0, 959341012135, 6733263775705, 14959233768155, 12544077286577, 3784893764835, 386169639954, 8047840951, 0] := by
  rw [show A10K2.u1929 = KTree.node A10K2.u1925 (nat_lit 30244360) (nat_lit 12779158875) (nat_lit 0) A10K2.u1928 from rfl, totK_node, atot1925, atot1928]
  decide +kernel

theorem arows1937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1937 = true := by
  rw [show A10K2.u1937 = KTree.node A10K2.u1933 (nat_lit 30354444) (nat_lit 4314644501) (nat_lit 0) A10K2.u1936 from rfl, allE_node, arows1933, irow1937, arows1936]
  all_goals rfl

theorem atot1937 : totK PA10K2 A10K2.u1937 = [0, 0, 2245520058772, 10357844932817, 16217520623458, 9509926145213, 1729486103761, 71696619774, 0, 0] := by
  rw [show A10K2.u1937 = KTree.node A10K2.u1933 (nat_lit 30354444) (nat_lit 4314644501) (nat_lit 0) A10K2.u1936 from rfl, totK_node, atot1933, atot1936]
  decide +kernel

theorem arows1944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1944 = true := by
  rw [show A10K2.u1944 = KTree.node A10K2.u1940 (nat_lit 30940002) (nat_lit 8048332076) (nat_lit 0) A10K2.u1943 from rfl, allE_node, arows1940, irow1944, arows1943]
  all_goals rfl

theorem atot1944 : totK PA10K2 A10K2.u1944 = [0, 2127308439256, 9363307030868, 14105587300745, 9165000524620, 3719629872352, 855968639255, 56100664475, 0, 0] := by
  rw [show A10K2.u1944 = KTree.node A10K2.u1940 (nat_lit 30940002) (nat_lit 8048332076) (nat_lit 0) A10K2.u1943 from rfl, totK_node, atot1940, atot1943]
  decide +kernel

theorem arows1953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1953 = true := by
  rw [show A10K2.u1953 = KTree.node A10K2.u1949 (nat_lit 30973028) (nat_lit 11028471565) (nat_lit 0) A10K2.u1952 from rfl, allE_node, arows1949, irow1953, arows1952]
  all_goals rfl

theorem atot1953 : totK PA10K2 A10K2.u1953 = [0, 409801074616, 4027405675171, 12557574199692, 15175817086523, 6178157204147, 806093837587, 30650496230, 0, 0] := by
  rw [show A10K2.u1953 = KTree.node A10K2.u1949 (nat_lit 30973028) (nat_lit 11028471565) (nat_lit 0) A10K2.u1952 from rfl, totK_node, atot1949, atot1952]
  decide +kernel

theorem arows1960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1960 = true := by
  rw [show A10K2.u1960 = KTree.node A10K2.u1956 (nat_lit 31026209) (nat_lit 9169857587) (nat_lit 0) A10K2.u1959 from rfl, allE_node, arows1956, irow1960, arows1959]
  all_goals rfl

theorem atot1960 : totK PA10K2 A10K2.u1960 = [0, 1466492540230, 8172364925136, 15610049202740, 11659419612679, 2949827366390, 183093315259, 0, 0, 0] := by
  rw [show A10K2.u1960 = KTree.node A10K2.u1956 (nat_lit 31026209) (nat_lit 9169857587) (nat_lit 0) A10K2.u1959 from rfl, totK_node, atot1956, atot1959]
  decide +kernel

theorem arows1968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1968 = true := by
  rw [show A10K2.u1968 = KTree.node A10K2.u1964 (nat_lit 31130376) (nat_lit 13965864106) (nat_lit 0) A10K2.u1967 from rfl, allE_node, arows1964, irow1968, arows1967]
  all_goals rfl

theorem atot1968 : totK PA10K2 A10K2.u1968 = [0, 1495542578372, 7505408831960, 13831609713009, 11630728445668, 4330844097839, 549340548330, 13576218110, 0, 0] := by
  rw [show A10K2.u1968 = KTree.node A10K2.u1964 (nat_lit 31130376) (nat_lit 13965864106) (nat_lit 0) A10K2.u1967 from rfl, totK_node, atot1964, atot1967]
  decide +kernel

theorem arows1975 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1975 = true := by
  rw [show A10K2.u1975 = KTree.node A10K2.u1971 (nat_lit 31161421) (nat_lit 3004634436) (nat_lit 0) A10K2.u1974 from rfl, allE_node, arows1971, irow1975, arows1974]
  all_goals rfl

theorem atot1975 : totK PA10K2 A10K2.u1975 = [0, 893295087998, 5928426393566, 13957588387453, 13371871968961, 4623149112601, 461233119597, 6904928264, 0, 0] := by
  rw [show A10K2.u1975 = KTree.node A10K2.u1971 (nat_lit 31161421) (nat_lit 3004634436) (nat_lit 0) A10K2.u1974 from rfl, totK_node, atot1971, atot1974]
  decide +kernel

theorem arows1985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1985 = true := by
  rw [show A10K2.u1985 = KTree.node A10K2.u1981 (nat_lit 31191966) (nat_lit 14990867186) (nat_lit 0) A10K2.u1984 from rfl, allE_node, arows1981, irow1985, arows1984]
  all_goals rfl

theorem atot1985 : totK PA10K2 A10K2.u1985 = [0, 0, 2019618876075, 9718591363433, 15839556889437, 9657946604364, 1879270886301, 98937591736, 0, 0] := by
  rw [show A10K2.u1985 = KTree.node A10K2.u1981 (nat_lit 31191966) (nat_lit 14990867186) (nat_lit 0) A10K2.u1984 from rfl, totK_node, atot1981, atot1984]
  decide +kernel

theorem arows1992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1992 = true := by
  rw [show A10K2.u1992 = KTree.node A10K2.u1988 (nat_lit 31225061) (nat_lit 1802874563) (nat_lit 0) A10K2.u1991 from rfl, allE_node, arows1988, irow1992, arows1991]
  all_goals rfl

theorem atot1992 : totK PA10K2 A10K2.u1992 = [0, 0, 1306029577408, 7359376775734, 14653950065443, 12017315604311, 3767058459881, 390655042939, 7007974415, 0] := by
  rw [show A10K2.u1992 = KTree.node A10K2.u1988 (nat_lit 31225061) (nat_lit 1802874563) (nat_lit 0) A10K2.u1991 from rfl, totK_node, atot1988, atot1991]
  decide +kernel

theorem arows2000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2000 = true := by
  rw [show A10K2.u2000 = KTree.node A10K2.u1996 (nat_lit 31274439) (nat_lit 13742678348) (nat_lit 0) A10K2.u1999 from rfl, allE_node, arows1996, irow2000, arows1999]
  all_goals rfl

theorem atot2000 : totK PA10K2 A10K2.u2000 = [0, 0, 1874295996104, 9366214492438, 15992104718037, 10499688360847, 2146612791129, 100177624927, 0, 0] := by
  rw [show A10K2.u2000 = KTree.node A10K2.u1996 (nat_lit 31274439) (nat_lit 13742678348) (nat_lit 0) A10K2.u1999 from rfl, totK_node, atot1996, atot1999]
  decide +kernel

theorem arows2007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2007 = true := by
  rw [show A10K2.u2007 = KTree.node A10K2.u2003 (nat_lit 31318960) (nat_lit 14310407619) (nat_lit 0) A10K2.u2006 from rfl, allE_node, arows2003, irow2007, arows2006]
  all_goals rfl

theorem atot2007 : totK PA10K2 A10K2.u2007 = [0, 0, 793614905159, 5848124005101, 14375478257690, 13915531883503, 4541633731014, 398414832031, 7151180950, 0] := by
  rw [show A10K2.u2007 = KTree.node A10K2.u2003 (nat_lit 31318960) (nat_lit 14310407619) (nat_lit 0) A10K2.u2006 from rfl, totK_node, atot2003, atot2006]
  decide +kernel

theorem arows2016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2016 = true := by
  rw [show A10K2.u2016 = KTree.node A10K2.u2012 (nat_lit 31419803) (nat_lit 9478330072) (nat_lit 0) A10K2.u2015 from rfl, allE_node, arows2012, irow2016, arows2015]
  all_goals rfl

theorem atot2016 : totK PA10K2 A10K2.u2016 = [0, 0, 1592238016509, 8312344043985, 15181627557453, 11378909560112, 2893305391982, 181661083820, 0, 0] := by
  rw [show A10K2.u2016 = KTree.node A10K2.u2012 (nat_lit 31419803) (nat_lit 9478330072) (nat_lit 0) A10K2.u2015 from rfl, totK_node, atot2012, atot2015]
  decide +kernel

theorem arows2023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2023 = true := by
  rw [show A10K2.u2023 = KTree.node A10K2.u2019 (nat_lit 31451036) (nat_lit 7977458716) (nat_lit 0) A10K2.u2022 from rfl, allE_node, arows2019, irow2023, arows2022]
  all_goals rfl

theorem atot2023 : totK PA10K2 A10K2.u2023 = [876250713213, 3080719290227, 3045804694393, 2398689159001, 7932612637228, 12768203924018, 7622478714879, 1450710932105, 73776485728, 0] := by
  rw [show A10K2.u2023 = KTree.node A10K2.u2019 (nat_lit 31451036) (nat_lit 7977458716) (nat_lit 0) A10K2.u2022 from rfl, totK_node, atot2019, atot2022]
  decide +kernel

theorem arows2031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2031 = true := by
  rw [show A10K2.u2031 = KTree.node A10K2.u2027 (nat_lit 38361642) (nat_lit 8424744497) (nat_lit 0) A10K2.u2030 from rfl, allE_node, arows2027, irow2031, arows2030]
  all_goals rfl

theorem atot2031 : totK PA10K2 A10K2.u2031 = [1508223463949, 8386844957321, 15749621166790, 10851416164512, 2356289484458, 126036536646, 0, 0, 0, 0] := by
  rw [show A10K2.u2031 = KTree.node A10K2.u2027 (nat_lit 38361642) (nat_lit 8424744497) (nat_lit 0) A10K2.u2030 from rfl, totK_node, atot2027, atot2030]
  decide +kernel

theorem arows2038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2038 = true := by
  rw [show A10K2.u2038 = KTree.node A10K2.u2034 (nat_lit 38392101) (nat_lit 7405569927) (nat_lit 0) A10K2.u2037 from rfl, allE_node, arows2034, irow2038, arows2037]
  all_goals rfl

theorem atot2038 : totK PA10K2 A10K2.u2038 = [424355675811, 3958406745064, 11725497932642, 14305018246285, 6549274154869, 936303292826, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2038 = KTree.node A10K2.u2034 (nat_lit 38392101) (nat_lit 7405569927) (nat_lit 0) A10K2.u2037 from rfl, totK_node, atot2034, atot2037]
  decide +kernel

theorem arows2053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2053 = true := by
  rw [show A10K2.u2053 = KTree.node A10K2.u2049 (nat_lit 38422167) (nat_lit 12084326520) (nat_lit 0) A10K2.u2052 from rfl, allE_node, arows2049, irow2053, arows2052]
  all_goals rfl

theorem atot2053 : totK PA10K2 A10K2.u2053 = [1578337948761, 8402698859244, 15278570264284, 10442926798894, 2186176899930, 108042545286, 0, 0, 0, 0] := by
  rw [show A10K2.u2053 = KTree.node A10K2.u2049 (nat_lit 38422167) (nat_lit 12084326520) (nat_lit 0) A10K2.u2052 from rfl, totK_node, atot2049, atot2052]
  decide +kernel

theorem arows2060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2060 = true := by
  rw [show A10K2.u2060 = KTree.node A10K2.u2056 (nat_lit 38473734) (nat_lit 14882822736) (nat_lit 0) A10K2.u2059 from rfl, allE_node, arows2056, irow2060, arows2059]
  all_goals rfl

theorem atot2060 : totK PA10K2 A10K2.u2060 = [1517298970217, 7694109442842, 14390957005053, 11540150136349, 3436521629808, 369085052807, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2060 = KTree.node A10K2.u2056 (nat_lit 38473734) (nat_lit 14882822736) (nat_lit 0) A10K2.u2059 from rfl, totK_node, atot2056, atot2059]
  decide +kernel

theorem arows2068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2068 = true := by
  rw [show A10K2.u2068 = KTree.node A10K2.u2064 (nat_lit 38506550) (nat_lit 15841531813) (nat_lit 0) A10K2.u2067 from rfl, allE_node, arows2064, irow2068, arows2067]
  all_goals rfl

theorem atot2068 : totK PA10K2 A10K2.u2068 = [613328696870, 4991208814808, 13316433507616, 14442274848512, 5970129926542, 726492845794, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u2068 = KTree.node A10K2.u2064 (nat_lit 38506550) (nat_lit 15841531813) (nat_lit 0) A10K2.u2067 from rfl, totK_node, atot2064, atot2067]
  decide +kernel

theorem arows2075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2075 = true := by
  rw [show A10K2.u2075 = KTree.node A10K2.u2071 (nat_lit 38612378) (nat_lit 14720781080) (nat_lit 0) A10K2.u2074 from rfl, allE_node, arows2071, irow2075, arows2074]
  all_goals rfl

theorem atot2075 : totK PA10K2 A10K2.u2075 = [0, 1919347076104, 9748574326865, 15921790795856, 9263852945615, 1735864193240, 92878874959, 0, 0, 0] := by
  rw [show A10K2.u2075 = KTree.node A10K2.u2071 (nat_lit 38612378) (nat_lit 14720781080) (nat_lit 0) A10K2.u2074 from rfl, totK_node, atot2071, atot2074]
  decide +kernel

theorem arows2084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2084 = true := by
  rw [show A10K2.u2084 = KTree.node A10K2.u2080 (nat_lit 38643646) (nat_lit 16023159446) (nat_lit 0) A10K2.u2083 from rfl, allE_node, arows2080, irow2084, arows2083]
  all_goals rfl

theorem atot2084 : totK PA10K2 A10K2.u2084 = [0, 784301050123, 5322686913219, 13344924112769, 13475441922869, 4942591949206, 678989798922, 31018567651, 0, 0] := by
  rw [show A10K2.u2084 = KTree.node A10K2.u2080 (nat_lit 38643646) (nat_lit 16023159446) (nat_lit 0) A10K2.u2083 from rfl, totK_node, atot2080, atot2083]
  decide +kernel

theorem arows2091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2091 = true := by
  rw [show A10K2.u2091 = KTree.node A10K2.u2087 (nat_lit 38675966) (nat_lit 15454607350) (nat_lit 0) A10K2.u2090 from rfl, allE_node, arows2087, irow2091, arows2090]
  all_goals rfl

theorem atot2091 : totK PA10K2 A10K2.u2091 = [0, 2002693624572, 8962175686665, 14255373277298, 9847360523993, 2801480991090, 276565484131, 5685526223, 0, 0] := by
  rw [show A10K2.u2091 = KTree.node A10K2.u2087 (nat_lit 38675966) (nat_lit 15454607350) (nat_lit 0) A10K2.u2090 from rfl, totK_node, atot2087, atot2090]
  decide +kernel

theorem arows2099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2099 = true := by
  rw [show A10K2.u2099 = KTree.node A10K2.u2095 (nat_lit 38715960) (nat_lit 8208443234) (nat_lit 0) A10K2.u2098 from rfl, allE_node, arows2095, irow2099, arows2098]
  all_goals rfl

theorem atot2099 : totK PA10K2 A10K2.u2099 = [0, 603357570004, 5624133333146, 14563358778288, 13109787576038, 3613098749626, 309703538650, 6239673734, 0, 0] := by
  rw [show A10K2.u2099 = KTree.node A10K2.u2095 (nat_lit 38715960) (nat_lit 8208443234) (nat_lit 0) A10K2.u2098 from rfl, totK_node, atot2095, atot2098]
  decide +kernel

theorem arows2106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2106 = true := by
  rw [show A10K2.u2106 = KTree.node A10K2.u2102 (nat_lit 38759597) (nat_lit 4130235660) (nat_lit 0) A10K2.u2105 from rfl, allE_node, arows2102, irow2106, arows2105]
  all_goals rfl

theorem atot2106 : totK PA10K2 A10K2.u2106 = [560981842138, 3955682668726, 10797079802702, 14072861768178, 8247187216648, 1720608480587, 93667527727, 0, 0, 0] := by
  rw [show A10K2.u2106 = KTree.node A10K2.u2102 (nat_lit 38759597) (nat_lit 4130235660) (nat_lit 0) A10K2.u2105 from rfl, totK_node, atot2102, atot2105]
  decide +kernel

theorem arows2116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2116 = true := by
  rw [show A10K2.u2116 = KTree.node A10K2.u2112 (nat_lit 38834176) (nat_lit 15792662511) (nat_lit 0) A10K2.u2115 from rfl, allE_node, arows2112, irow2116, arows2115]
  all_goals rfl

theorem atot2116 : totK PA10K2 A10K2.u2116 = [1055664103064, 5934686207504, 12726922568697, 12210214081950, 4876252559824, 762246184473, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u2116 = KTree.node A10K2.u2112 (nat_lit 38834176) (nat_lit 15792662511) (nat_lit 0) A10K2.u2115 from rfl, totK_node, atot2112, atot2115]
  decide +kernel

theorem arows2123 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2123 = true := by
  rw [show A10K2.u2123 = KTree.node A10K2.u2119 (nat_lit 38881952) (nat_lit 8543417959) (nat_lit 0) A10K2.u2122 from rfl, allE_node, arows2119, irow2123, arows2122]
  all_goals rfl

theorem atot2123 : totK PA10K2 A10K2.u2123 = [1879963097768, 9479480207158, 15945531205953, 9772845537053, 1873840683115, 93364209514, 0, 0, 0, 0] := by
  rw [show A10K2.u2123 = KTree.node A10K2.u2119 (nat_lit 38881952) (nat_lit 8543417959) (nat_lit 0) A10K2.u2122 from rfl, totK_node, atot2119, atot2122]
  decide +kernel

theorem arows2131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2131 = true := by
  rw [show A10K2.u2131 = KTree.node A10K2.u2127 (nat_lit 38914717) (nat_lit 5879602105) (nat_lit 0) A10K2.u2130 from rfl, allE_node, arows2127, irow2131, arows2130]
  all_goals rfl

theorem atot2131 : totK PA10K2 A10K2.u2131 = [582799510374, 4225141136222, 11615836390672, 14111803145311, 6612833411061, 951231485528, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2131 = KTree.node A10K2.u2127 (nat_lit 38914717) (nat_lit 5879602105) (nat_lit 0) A10K2.u2130 from rfl, totK_node, atot2127, atot2130]
  decide +kernel

theorem arows2138 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2138 = true := by
  rw [show A10K2.u2138 = KTree.node A10K2.u2134 (nat_lit 38945549) (nat_lit 5871483923) (nat_lit 0) A10K2.u2137 from rfl, allE_node, arows2134, irow2138, arows2137]
  all_goals rfl

theorem atot2138 : totK PA10K2 A10K2.u2138 = [1591323679956, 8601188760241, 15474834935919, 10162024903648, 2010043212121, 87667327821, 0, 0, 0, 0] := by
  rw [show A10K2.u2138 = KTree.node A10K2.u2134 (nat_lit 38945549) (nat_lit 5871483923) (nat_lit 0) A10K2.u2137 from rfl, totK_node, atot2134, atot2137]
  decide +kernel

theorem arows2147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2147 = true := by
  rw [show A10K2.u2147 = KTree.node A10K2.u2143 (nat_lit 39059754) (nat_lit 9154230619) (nat_lit 0) A10K2.u2146 from rfl, allE_node, arows2143, irow2147, arows2146]
  all_goals rfl

theorem atot2147 : totK PA10K2 A10K2.u2147 = [0, 2583597137470, 11399612278439, 15668811690251, 6980144144153, 1000161231696, 37172849495, 0, 0, 0] := by
  rw [show A10K2.u2147 = KTree.node A10K2.u2143 (nat_lit 39059754) (nat_lit 9154230619) (nat_lit 0) A10K2.u2146 from rfl, totK_node, atot2143, atot2146]
  decide +kernel

theorem arows2154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2154 = true := by
  rw [show A10K2.u2154 = KTree.node A10K2.u2150 (nat_lit 39142179) (nat_lit 8941990552) (nat_lit 0) A10K2.u2153 from rfl, allE_node, arows2150, irow2154, arows2153]
  all_goals rfl

theorem atot2154 : totK PA10K2 A10K2.u2154 = [0, 2196809829182, 10172134417172, 15888950771190, 8853642975405, 1432219435141, 51124281457, 0, 0, 0] := by
  rw [show A10K2.u2154 = KTree.node A10K2.u2150 (nat_lit 39142179) (nat_lit 8941990552) (nat_lit 0) A10K2.u2153 from rfl, totK_node, atot2150, atot2153]
  decide +kernel

theorem arows2162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2162 = true := by
  rw [show A10K2.u2162 = KTree.node A10K2.u2158 (nat_lit 39202495) (nat_lit 12927711087) (nat_lit 0) A10K2.u2161 from rfl, allE_node, arows2158, irow2162, arows2161]
  all_goals rfl

theorem atot2162 : totK PA10K2 A10K2.u2162 = [0, 2171513690309, 10336659945067, 15785672332661, 8076667089412, 1232488391237, 61078328232, 0, 0, 0] := by
  rw [show A10K2.u2162 = KTree.node A10K2.u2158 (nat_lit 39202495) (nat_lit 12927711087) (nat_lit 0) A10K2.u2161 from rfl, totK_node, atot2158, atot2161]
  decide +kernel

theorem arows2169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2169 = true := by
  rw [show A10K2.u2169 = KTree.node A10K2.u2165 (nat_lit 39242017) (nat_lit 9700014513) (nat_lit 0) A10K2.u2168 from rfl, allE_node, arows2165, irow2169, arows2168]
  all_goals rfl

theorem atot2169 : totK PA10K2 A10K2.u2169 = [953763886815, 3852874007705, 7531507555997, 11348148774461, 10409222237284, 3447811974605, 384962563863, 6354482628, 0, 0] := by
  rw [show A10K2.u2169 = KTree.node A10K2.u2165 (nat_lit 39242017) (nat_lit 9700014513) (nat_lit 0) A10K2.u2168 from rfl, totK_node, atot2165, atot2168]
  decide +kernel

theorem arows2180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2180 = true := by
  rw [show A10K2.u2180 = KTree.node A10K2.u2176 (nat_lit 39358856) (nat_lit 14332909434) (nat_lit 0) A10K2.u2179 from rfl, allE_node, arows2176, irow2180, arows2179]
  all_goals rfl

theorem atot2180 : totK PA10K2 A10K2.u2180 = [1279371604598, 7237630370085, 14473822456635, 12577853247463, 4333090211687, 545793753298, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u2180 = KTree.node A10K2.u2176 (nat_lit 39358856) (nat_lit 14332909434) (nat_lit 0) A10K2.u2179 from rfl, totK_node, atot2176, atot2179]
  decide +kernel

theorem arows2187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2187 = true := by
  rw [show A10K2.u2187 = KTree.node A10K2.u2183 (nat_lit 39413425) (nat_lit 5116158706) (nat_lit 0) A10K2.u2186 from rfl, allE_node, arows2183, irow2187, arows2186]
  all_goals rfl

theorem atot2187 : totK PA10K2 A10K2.u2187 = [1371842486777, 7971872652049, 15703884413487, 11614204519740, 2619426949260, 133625252564, 0, 0, 0, 0] := by
  rw [show A10K2.u2187 = KTree.node A10K2.u2183 (nat_lit 39413425) (nat_lit 5116158706) (nat_lit 0) A10K2.u2186 from rfl, totK_node, atot2183, atot2186]
  decide +kernel

theorem arows2195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2195 = true := by
  rw [show A10K2.u2195 = KTree.node A10K2.u2191 (nat_lit 39445846) (nat_lit 11830423920) (nat_lit 0) A10K2.u2194 from rfl, allE_node, arows2191, irow2195, arows2194]
  all_goals rfl

theorem atot2195 : totK PA10K2 A10K2.u2195 = [1030278054533, 5622191581101, 12389225941789, 13175456982229, 6002383830939, 908581719970, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2195 = KTree.node A10K2.u2191 (nat_lit 39445846) (nat_lit 11830423920) (nat_lit 0) A10K2.u2194 from rfl, totK_node, atot2191, atot2194]
  decide +kernel

theorem arows2202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2202 = true := by
  rw [show A10K2.u2202 = KTree.node A10K2.u2198 (nat_lit 39546881) (nat_lit 10590452259) (nat_lit 0) A10K2.u2201 from rfl, allE_node, arows2198, irow2202, arows2201]
  all_goals rfl

theorem atot2202 : totK PA10K2 A10K2.u2202 = [1254436619767, 7216240137863, 14581438914749, 12293683865940, 4012803852477, 425610689120, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u2202 = KTree.node A10K2.u2198 (nat_lit 39546881) (nat_lit 10590452259) (nat_lit 0) A10K2.u2201 from rfl, totK_node, atot2198, atot2201]
  decide +kernel

theorem arows2211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2211 = true := by
  rw [show A10K2.u2211 = KTree.node A10K2.u2207 (nat_lit 39579249) (nat_lit 7929323276) (nat_lit 0) A10K2.u2210 from rfl, allE_node, arows2207, irow2211, arows2210]
  all_goals rfl

theorem atot2211 : totK PA10K2 A10K2.u2211 = [0, 2069335505316, 10094337157604, 16161844012744, 9526799080413, 1789515740454, 93490405862, 0, 0, 0] := by
  rw [show A10K2.u2211 = KTree.node A10K2.u2207 (nat_lit 39579249) (nat_lit 7929323276) (nat_lit 0) A10K2.u2210 from rfl, totK_node, atot2207, atot2210]
  decide +kernel

theorem arows2218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2218 = true := by
  rw [show A10K2.u2218 = KTree.node A10K2.u2214 (nat_lit 39620023) (nat_lit 15197340579) (nat_lit 0) A10K2.u2217 from rfl, allE_node, arows2214, irow2218, arows2217]
  all_goals rfl

theorem atot2218 : totK PA10K2 A10K2.u2218 = [0, 1555361734131, 7642194882988, 14254721065624, 12234259241361, 4172007476091, 437501318025, 7007974415, 0, 0] := by
  rw [show A10K2.u2218 = KTree.node A10K2.u2214 (nat_lit 39620023) (nat_lit 15197340579) (nat_lit 0) A10K2.u2217 from rfl, totK_node, atot2214, atot2217]
  decide +kernel

theorem arows2226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2226 = true := by
  rw [show A10K2.u2226 = KTree.node A10K2.u2222 (nat_lit 39674426) (nat_lit 10015028066) (nat_lit 0) A10K2.u2225 from rfl, allE_node, arows2222, irow2226, arows2225]
  all_goals rfl

theorem atot2226 : totK PA10K2 A10K2.u2226 = [0, 1440753030250, 8339052901191, 15930284484577, 11126590172526, 2384150636997, 125967028565, 0, 0, 0] := by
  rw [show A10K2.u2226 = KTree.node A10K2.u2222 (nat_lit 39674426) (nat_lit 10015028066) (nat_lit 0) A10K2.u2225 from rfl, totK_node, atot2222, atot2225]
  decide +kernel

theorem arows2233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2233 = true := by
  rw [show A10K2.u2233 = KTree.node A10K2.u2229 (nat_lit 39710455) (nat_lit 14516957277) (nat_lit 0) A10K2.u2232 from rfl, allE_node, arows2229, irow2233, arows2232]
  all_goals rfl

theorem atot2233 : totK PA10K2 A10K2.u2233 = [0, 1410410053387, 7582541148144, 14516163557634, 11940719765577, 3916968616578, 396794164369, 7151180950, 0, 0] := by
  rw [show A10K2.u2233 = KTree.node A10K2.u2229 (nat_lit 39710455) (nat_lit 14516957277) (nat_lit 0) A10K2.u2232 from rfl, totK_node, atot2229, atot2232]
  decide +kernel

theorem arows2243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2243 = true := by
  rw [show A10K2.u2243 = KTree.node A10K2.u2239 (nat_lit 39812153) (nat_lit 7244271112) (nat_lit 0) A10K2.u2242 from rfl, allE_node, arows2239, irow2243, arows2242]
  all_goals rfl

theorem atot2243 : totK PA10K2 A10K2.u2243 = [0, 872810143373, 6149610538774, 14528818753513, 13473194298900, 4266554093979, 371921640558, 6318667960, 0, 0] := by
  rw [show A10K2.u2243 = KTree.node A10K2.u2239 (nat_lit 39812153) (nat_lit 7244271112) (nat_lit 0) A10K2.u2242 from rfl, totK_node, atot2239, atot2242]
  decide +kernel

theorem arows2250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2250 = true := by
  rw [show A10K2.u2250 = KTree.node A10K2.u2246 (nat_lit 39844928) (nat_lit 15065041195) (nat_lit 0) A10K2.u2249 from rfl, allE_node, arows2246, irow2250, arows2249]
  all_goals rfl

theorem atot2250 : totK PA10K2 A10K2.u2250 = [0, 1021347070404, 5279030493937, 11537187114426, 12983048454250, 6832479088293, 1292219124220, 67457817768, 0, 0] := by
  rw [show A10K2.u2250 = KTree.node A10K2.u2246 (nat_lit 39844928) (nat_lit 15065041195) (nat_lit 0) A10K2.u2249 from rfl, totK_node, atot2246, atot2249]
  decide +kernel

theorem arows2258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2258 = true := by
  rw [show A10K2.u2258 = KTree.node A10K2.u2254 (nat_lit 40464454) (nat_lit 14943008976) (nat_lit 0) A10K2.u2257 from rfl, allE_node, arows2254, irow2258, arows2257]
  all_goals rfl

theorem atot2258 : totK PA10K2 A10K2.u2258 = [0, 1359421431257, 7549890454595, 14540204128606, 11384683471006, 3569077696269, 478752013663, 25565504801, 0, 0] := by
  rw [show A10K2.u2258 = KTree.node A10K2.u2254 (nat_lit 40464454) (nat_lit 14943008976) (nat_lit 0) A10K2.u2257 from rfl, totK_node, atot2254, atot2257]
  decide +kernel

theorem arows2265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2265 = true := by
  rw [show A10K2.u2265 = KTree.node A10K2.u2261 (nat_lit 40496196) (nat_lit 3565234873) (nat_lit 0) A10K2.u2264 from rfl, allE_node, arows2261, irow2265, arows2264]
  all_goals rfl

theorem atot2265 : totK PA10K2 A10K2.u2265 = [0, 1227264424580, 6661619410165, 13300914511822, 11926359679085, 4425856753744, 503903591511, 11638555097, 0, 0] := by
  rw [show A10K2.u2265 = KTree.node A10K2.u2261 (nat_lit 40496196) (nat_lit 3565234873) (nat_lit 0) A10K2.u2264 from rfl, totK_node, atot2261, atot2264]
  decide +kernel

theorem arows2274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2274 = true := by
  rw [show A10K2.u2274 = KTree.node A10K2.u2270 (nat_lit 40534378) (nat_lit 6048839698) (nat_lit 0) A10K2.u2273 from rfl, allE_node, arows2270, irow2274, arows2273]
  all_goals rfl

theorem atot2274 : totK PA10K2 A10K2.u2274 = [0, 773611290687, 6104596701947, 14833529675986, 12666321008644, 2930856138078, 138329377792, 0, 0, 0] := by
  rw [show A10K2.u2274 = KTree.node A10K2.u2270 (nat_lit 40534378) (nat_lit 6048839698) (nat_lit 0) A10K2.u2273 from rfl, totK_node, atot2270, atot2273]
  decide +kernel

theorem arows2281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2281 = true := by
  rw [show A10K2.u2281 = KTree.node A10K2.u2277 (nat_lit 40579036) (nat_lit 2567440050) (nat_lit 0) A10K2.u2280 from rfl, allE_node, arows2277, irow2281, arows2280]
  all_goals rfl

theorem atot2281 : totK PA10K2 A10K2.u2281 = [0, 2129691131741, 9629786180331, 15235355935298, 9916953100552, 2528808659246, 248964045851, 6354482628, 0, 0] := by
  rw [show A10K2.u2281 = KTree.node A10K2.u2277 (nat_lit 40579036) (nat_lit 2567440050) (nat_lit 0) A10K2.u2280 from rfl, totK_node, atot2277, atot2280]
  decide +kernel

theorem arows2289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2289 = true := by
  rw [show A10K2.u2289 = KTree.node A10K2.u2285 (nat_lit 40613226) (nat_lit 9846111812) (nat_lit 0) A10K2.u2288 from rfl, allE_node, arows2285, irow2289, arows2288]
  all_goals rfl

theorem atot2289 : totK PA10K2 A10K2.u2289 = [0, 0, 2450325370379, 11089680134318, 16408502918687, 8609836970302, 1265124842706, 24696255293, 0, 0] := by
  rw [show A10K2.u2289 = KTree.node A10K2.u2285 (nat_lit 40613226) (nat_lit 9846111812) (nat_lit 0) A10K2.u2288 from rfl, totK_node, atot2285, atot2288]
  decide +kernel

theorem arows2296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2296 = true := by
  rw [show A10K2.u2296 = KTree.node A10K2.u2292 (nat_lit 40716072) (nat_lit 9552753253) (nat_lit 0) A10K2.u2295 from rfl, allE_node, arows2292, irow2296, arows2295]
  all_goals rfl

theorem atot2296 : totK PA10K2 A10K2.u2296 = [0, 0, 2364197701451, 10759370538037, 15910066931895, 8144602683356, 1301373803611, 68452230123, 0, 0] := by
  rw [show A10K2.u2296 = KTree.node A10K2.u2292 (nat_lit 40716072) (nat_lit 9552753253) (nat_lit 0) A10K2.u2295 from rfl, totK_node, atot2292, atot2295]
  decide +kernel

theorem arows2308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2308 = true := by
  rw [show A10K2.u2308 = KTree.node A10K2.u2304 (nat_lit 40748503) (nat_lit 13161532576) (nat_lit 0) A10K2.u2307 from rfl, allE_node, arows2304, irow2308, arows2307]
  all_goals rfl

theorem atot2308 : totK PA10K2 A10K2.u2308 = [0, 0, 424355675811, 4151778815281, 12151710475580, 13965414926970, 5941629356827, 888575063418, 36704093874, 0] := by
  rw [show A10K2.u2308 = KTree.node A10K2.u2304 (nat_lit 40748503) (nat_lit 13161532576) (nat_lit 0) A10K2.u2307 from rfl, totK_node, atot2304, atot2307]
  decide +kernel

theorem arows2315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2315 = true := by
  rw [show A10K2.u2315 = KTree.node A10K2.u2311 (nat_lit 40781040) (nat_lit 4597072967) (nat_lit 0) A10K2.u2314 from rfl, allE_node, arows2311, irow2315, arows2314]
  all_goals rfl

theorem atot2315 : totK PA10K2 A10K2.u2315 = [0, 0, 1570230833141, 8631015661155, 15639567686937, 9800321621654, 1734740950916, 82062653739, 0, 0] := by
  rw [show A10K2.u2315 = KTree.node A10K2.u2311 (nat_lit 40781040) (nat_lit 4597072967) (nat_lit 0) A10K2.u2314 from rfl, totK_node, atot2311, atot2314]
  decide +kernel

theorem arows2323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2323 = true := by
  rw [show A10K2.u2323 = KTree.node A10K2.u2319 (nat_lit 40838893) (nat_lit 5371804500) (nat_lit 0) A10K2.u2322 from rfl, allE_node, arows2319, irow2323, arows2322]
  all_goals rfl

theorem atot2323 : totK PA10K2 A10K2.u2323 = [0, 0, 2121636719949, 9255121674060, 14641102324145, 9975997470956, 2606000428213, 257763232781, 5982052406, 0] := by
  rw [show A10K2.u2323 = KTree.node A10K2.u2319 (nat_lit 40838893) (nat_lit 5371804500) (nat_lit 0) A10K2.u2322 from rfl, totK_node, atot2319, atot2322]
  decide +kernel

theorem arows2330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2330 = true := by
  rw [show A10K2.u2330 = KTree.node A10K2.u2326 (nat_lit 40912019) (nat_lit 10954712508) (nat_lit 0) A10K2.u2329 from rfl, allE_node, arows2326, irow2330, arows2329]
  all_goals rfl

theorem atot2330 : totK PA10K2 A10K2.u2330 = [0, 1299799213788, 7057503150544, 13660964827451, 11273563608962, 4261527414543, 773335669643, 41590655314, 0, 0] := by
  rw [show A10K2.u2330 = KTree.node A10K2.u2326 (nat_lit 40912019) (nat_lit 10954712508) (nat_lit 0) A10K2.u2329 from rfl, totK_node, atot2326, atot2329]
  decide +kernel

theorem arows2339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2339 = true := by
  rw [show A10K2.u2339 = KTree.node A10K2.u2335 (nat_lit 40974614) (nat_lit 10062307126) (nat_lit 0) A10K2.u2338 from rfl, allE_node, arows2335, irow2339, arows2338]
  all_goals rfl

theorem atot2339 : totK PA10K2 A10K2.u2339 = [0, 2151265346480, 9359268857358, 14560581935190, 9502926993580, 2439815055978, 230001368864, 5546304973, 0, 0] := by
  rw [show A10K2.u2339 = KTree.node A10K2.u2335 (nat_lit 40974614) (nat_lit 10062307126) (nat_lit 0) A10K2.u2338 from rfl, totK_node, atot2335, atot2338]
  decide +kernel

theorem arows2346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2346 = true := by
  rw [show A10K2.u2346 = KTree.node A10K2.u2342 (nat_lit 41007325) (nat_lit 5725859541) (nat_lit 0) A10K2.u2345 from rfl, allE_node, arows2342, irow2346, arows2345]
  all_goals rfl

theorem atot2346 : totK PA10K2 A10K2.u2346 = [0, 45544482702, 3290279611804, 12406563438512, 15385466230022, 6573734101570, 917887274922, 37204059898, 0, 0] := by
  rw [show A10K2.u2346 = KTree.node A10K2.u2342 (nat_lit 41007325) (nat_lit 5725859541) (nat_lit 0) A10K2.u2345 from rfl, totK_node, atot2342, atot2345]
  decide +kernel

theorem arows2354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2354 = true := by
  rw [show A10K2.u2354 = KTree.node A10K2.u2350 (nat_lit 41037485) (nat_lit 5857810298) (nat_lit 0) A10K2.u2353 from rfl, allE_node, arows2350, irow2354, arows2353]
  all_goals rfl

theorem atot2354 : totK PA10K2 A10K2.u2354 = [0, 2174123190330, 9986137226975, 15214401270517, 8711111628645, 1753681844499, 97939164757, 0, 0, 0] := by
  rw [show A10K2.u2354 = KTree.node A10K2.u2350 (nat_lit 41037485) (nat_lit 5857810298) (nat_lit 0) A10K2.u2353 from rfl, totK_node, atot2350, atot2353]
  decide +kernel

theorem arows2361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2361 = true := by
  rw [show A10K2.u2361 = KTree.node A10K2.u2357 (nat_lit 41076549) (nat_lit 6303593301) (nat_lit 0) A10K2.u2360 from rfl, allE_node, arows2357, irow2361, arows2360]
  all_goals rfl

theorem atot2361 : totK PA10K2 A10K2.u2361 = [0, 0, 3042726931759, 12599547193112, 15511324728821, 5674674695444, 632027428648, 11801668502, 0, 0] := by
  rw [show A10K2.u2361 = KTree.node A10K2.u2357 (nat_lit 41076549) (nat_lit 6303593301) (nat_lit 0) A10K2.u2360 from rfl, totK_node, atot2357, atot2360]
  decide +kernel

theorem arows2371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2371 = true := by
  rw [show A10K2.u2371 = KTree.node A10K2.u2367 (nat_lit 41235816) (nat_lit 6991964254) (nat_lit 0) A10K2.u2370 from rfl, allE_node, arows2367, irow2371, arows2370]
  all_goals rfl

theorem atot2371 : totK PA10K2 A10K2.u2371 = [0, 0, 2398387259023, 10706961330122, 15801376983942, 7798575543522, 1116841704095, 44161539106, 0, 0] := by
  rw [show A10K2.u2371 = KTree.node A10K2.u2367 (nat_lit 41235816) (nat_lit 6991964254) (nat_lit 0) A10K2.u2370 from rfl, totK_node, atot2367, atot2370]
  decide +kernel

theorem arows2378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2378 = true := by
  rw [show A10K2.u2378 = KTree.node A10K2.u2374 (nat_lit 41297351) (nat_lit 5283101356) (nat_lit 0) A10K2.u2377 from rfl, allE_node, arows2374, irow2378, arows2377]
  all_goals rfl

theorem atot2378 : totK PA10K2 A10K2.u2378 = [0, 0, 2464984666664, 11067074615139, 15926752859380, 7600856292685, 1091357547750, 43426679930, 0, 0] := by
  rw [show A10K2.u2378 = KTree.node A10K2.u2374 (nat_lit 41297351) (nat_lit 5283101356) (nat_lit 0) A10K2.u2377 from rfl, totK_node, atot2374, atot2377]
  decide +kernel

theorem arows2386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2386 = true := by
  rw [show A10K2.u2386 = KTree.node A10K2.u2382 (nat_lit 41337605) (nat_lit 6920038188) (nat_lit 0) A10K2.u2385 from rfl, allE_node, arows2382, irow2386, arows2385]
  all_goals rfl

theorem atot2386 : totK PA10K2 A10K2.u2386 = [0, 591294713498, 2465630538831, 6699552550080, 13085427662187, 11040983054443, 3103658350217, 302189231664, 6354482628, 0] := by
  rw [show A10K2.u2386 = KTree.node A10K2.u2382 (nat_lit 41337605) (nat_lit 6920038188) (nat_lit 0) A10K2.u2385 from rfl, totK_node, atot2382, atot2385]
  decide +kernel

theorem arows2393 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2393 = true := by
  rw [show A10K2.u2393 = KTree.node A10K2.u2389 (nat_lit 41452385) (nat_lit 8999753644) (nat_lit 0) A10K2.u2392 from rfl, allE_node, arows2389, irow2393, arows2392]
  all_goals rfl

theorem atot2393 : totK PA10K2 A10K2.u2393 = [0, 1342722466589, 7286182194238, 14456676901275, 12645342563647, 4248060196331, 438604310885, 7237400819, 0, 0] := by
  rw [show A10K2.u2393 = KTree.node A10K2.u2389 (nat_lit 41452385) (nat_lit 8999753644) (nat_lit 0) A10K2.u2392 from rfl, totK_node, atot2389, atot2392]
  decide +kernel

theorem arows2402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2402 = true := by
  rw [show A10K2.u2402 = KTree.node A10K2.u2398 (nat_lit 41507648) (nat_lit 10481072590) (nat_lit 0) A10K2.u2401 from rfl, allE_node, arows2398, irow2402, arows2401]
  all_goals rfl

theorem atot2402 : totK PA10K2 A10K2.u2402 = [0, 1666428676533, 8853116643234, 15850837378009, 10637637842026, 2302960330717, 126942028378, 0, 0, 0] := by
  rw [show A10K2.u2402 = KTree.node A10K2.u2398 (nat_lit 41507648) (nat_lit 10481072590) (nat_lit 0) A10K2.u2401 from rfl, totK_node, atot2398, atot2401]
  decide +kernel

theorem arows2409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2409 = true := by
  rw [show A10K2.u2409 = KTree.node A10K2.u2405 (nat_lit 41539936) (nat_lit 11608927777) (nat_lit 0) A10K2.u2408 from rfl, allE_node, arows2405, irow2409, arows2408]
  all_goals rfl

theorem atot2409 : totK PA10K2 A10K2.u2409 = [0, 625736493037, 4718454432735, 12595198030426, 14091802017651, 6126229386307, 892101066529, 36968589557, 0, 0] := by
  rw [show A10K2.u2409 = KTree.node A10K2.u2405 (nat_lit 41539936) (nat_lit 11608927777) (nat_lit 0) A10K2.u2408 from rfl, totK_node, atot2405, atot2408]
  decide +kernel

theorem arows2417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2417 = true := by
  rw [show A10K2.u2417 = KTree.node A10K2.u2413 (nat_lit 41641879) (nat_lit 14322617938) (nat_lit 0) A10K2.u2416 from rfl, allE_node, arows2413, irow2417, arows2416]
  all_goals rfl

theorem atot2417 : totK PA10K2 A10K2.u2417 = [0, 1658046532202, 8366931777178, 15182781320832, 11382172230051, 2975901238239, 176848696347, 0, 0, 0] := by
  rw [show A10K2.u2417 = KTree.node A10K2.u2413 (nat_lit 41641879) (nat_lit 14322617938) (nat_lit 0) A10K2.u2416 from rfl, totK_node, atot2413, atot2416]
  decide +kernel

theorem arows2424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2424 = true := by
  rw [show A10K2.u2424 = KTree.node A10K2.u2420 (nat_lit 41674199) (nat_lit 14300367555) (nat_lit 0) A10K2.u2423 from rfl, allE_node, arows2420, irow2424, arows2423]
  all_goals rfl

theorem atot2424 : totK PA10K2 A10K2.u2424 = [796021182214, 2610860683949, 4097271329765, 8685793259679, 13308484244091, 8198400302737, 1562780801609, 74789331576, 0, 0] := by
  rw [show A10K2.u2424 = KTree.node A10K2.u2420 (nat_lit 41674199) (nat_lit 14300367555) (nat_lit 0) A10K2.u2423 from rfl, totK_node, atot2420, atot2423]
  decide +kernel

theorem arows2435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2435 = true := by
  rw [show A10K2.u2435 = KTree.node A10K2.u2431 (nat_lit 41965797) (nat_lit 7136786097) (nat_lit 0) A10K2.u2434 from rfl, allE_node, arows2431, irow2435, arows2434]
  all_goals rfl

theorem atot2435 : totK PA10K2 A10K2.u2435 = [1384286872291, 8247118770311, 15887914335218, 10959360718555, 2301886562728, 124309149834, 0, 0, 0, 0] := by
  rw [show A10K2.u2435 = KTree.node A10K2.u2431 (nat_lit 41965797) (nat_lit 7136786097) (nat_lit 0) A10K2.u2434 from rfl, totK_node, atot2431, atot2434]
  decide +kernel

theorem arows2442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2442 = true := by
  rw [show A10K2.u2442 = KTree.node A10K2.u2438 (nat_lit 41998856) (nat_lit 12461233422) (nat_lit 0) A10K2.u2441 from rfl, allE_node, arows2438, irow2442, arows2441]
  all_goals rfl

theorem atot2442 : totK PA10K2 A10K2.u2442 = [767063984985, 4816428170727, 12090956226185, 13720526821817, 6012237346290, 876387580861, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u2442 = KTree.node A10K2.u2438 (nat_lit 41998856) (nat_lit 12461233422) (nat_lit 0) A10K2.u2441 from rfl, totK_node, atot2438, atot2441]
  decide +kernel

theorem arows2450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2450 = true := by
  rw [show A10K2.u2450 = KTree.node A10K2.u2446 (nat_lit 42093341) (nat_lit 6299948848) (nat_lit 0) A10K2.u2449 from rfl, allE_node, arows2446, irow2450, arows2449]
  all_goals rfl

theorem atot2450 : totK PA10K2 A10K2.u2450 = [1380631111097, 8121037040390, 15539128637656, 10862375033105, 2365244705823, 114837853606, 0, 0, 0, 0] := by
  rw [show A10K2.u2450 = KTree.node A10K2.u2446 (nat_lit 42093341) (nat_lit 6299948848) (nat_lit 0) A10K2.u2449 from rfl, totK_node, atot2446, atot2449]
  decide +kernel

theorem arows2457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2457 = true := by
  rw [show A10K2.u2457 = KTree.node A10K2.u2453 (nat_lit 42208841) (nat_lit 6795308320) (nat_lit 0) A10K2.u2456 from rfl, allE_node, arows2453, irow2457, arows2456]
  all_goals rfl

theorem atot2457 : totK PA10K2 A10K2.u2457 = [0, 2187772925415, 10569555570431, 16042465541827, 7676130755242, 1089094390463, 37186156514, 0, 0, 0] := by
  rw [show A10K2.u2457 = KTree.node A10K2.u2453 (nat_lit 42208841) (nat_lit 6795308320) (nat_lit 0) A10K2.u2456 from rfl, totK_node, atot2453, atot2456]
  decide +kernel

theorem arows2466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2466 = true := by
  rw [show A10K2.u2466 = KTree.node A10K2.u2462 (nat_lit 42241976) (nat_lit 13898329239) (nat_lit 0) A10K2.u2465 from rfl, allE_node, arows2462, irow2466, arows2465]
  all_goals rfl

theorem atot2466 : totK PA10K2 A10K2.u2466 = [0, 592958361815, 4542460404618, 12387165638136, 13938469245147, 5727681645821, 844126801248, 36134558889, 0, 0] := by
  rw [show A10K2.u2466 = KTree.node A10K2.u2462 (nat_lit 42241976) (nat_lit 13898329239) (nat_lit 0) A10K2.u2465 from rfl, totK_node, atot2462, atot2465]
  decide +kernel

theorem arows2473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2473 = true := by
  rw [show A10K2.u2473 = KTree.node A10K2.u2469 (nat_lit 42345882) (nat_lit 15023698103) (nat_lit 0) A10K2.u2472 from rfl, allE_node, arows2469, irow2473, arows2472]
  all_goals rfl

theorem atot2473 : totK PA10K2 A10K2.u2473 = [0, 2146568976312, 10129982857223, 15798294377714, 8818702913177, 1550010491038, 80777338632, 0, 0, 0] := by
  rw [show A10K2.u2473 = KTree.node A10K2.u2469 (nat_lit 42345882) (nat_lit 15023698103) (nat_lit 0) A10K2.u2472 from rfl, totK_node, atot2469, atot2472]
  decide +kernel

theorem arows2481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2481 = true := by
  rw [show A10K2.u2481 = KTree.node A10K2.u2477 (nat_lit 42387747) (nat_lit 10113266383) (nat_lit 0) A10K2.u2480 from rfl, allE_node, arows2477, irow2481, arows2480]
  all_goals rfl

theorem atot2481 : totK PA10K2 A10K2.u2481 = [860205094993, 3736700297015, 7803410048455, 11946820129483, 10324789258471, 3030417579054, 274073213902, 5676195732, 0, 0] := by
  rw [show A10K2.u2481 = KTree.node A10K2.u2477 (nat_lit 42387747) (nat_lit 10113266383) (nat_lit 0) A10K2.u2480 from rfl, totK_node, atot2477, atot2480]
  decide +kernel

theorem arows2488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2488 = true := by
  rw [show A10K2.u2488 = KTree.node A10K2.u2484 (nat_lit 42560966) (nat_lit 15871218281) (nat_lit 0) A10K2.u2487 from rfl, allE_node, arows2484, irow2488, arows2487]
  all_goals rfl

theorem atot2488 : totK PA10K2 A10K2.u2488 = [1438061005852, 7827257846050, 14780683378558, 11339173799260, 3444796200735, 447535033592, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u2488 = KTree.node A10K2.u2484 (nat_lit 42560966) (nat_lit 15871218281) (nat_lit 0) A10K2.u2487 from rfl, totK_node, atot2484, atot2487]
  decide +kernel

theorem arows2498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2498 = true := by
  rw [show A10K2.u2498 = KTree.node A10K2.u2494 (nat_lit 42592154) (nat_lit 14875845437) (nat_lit 0) A10K2.u2497 from rfl, allE_node, arows2494, irow2498, arows2497]
  all_goals rfl

theorem atot2498 : totK PA10K2 A10K2.u2498 = [1224509320527, 6274012932885, 12694790781773, 12389614106674, 4989524177302, 574183559716, 11638555097, 0, 0, 0] := by
  rw [show A10K2.u2498 = KTree.node A10K2.u2494 (nat_lit 42592154) (nat_lit 14875845437) (nat_lit 0) A10K2.u2497 from rfl, totK_node, atot2494, atot2497]
  decide +kernel

theorem arows2505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2505 = true := by
  rw [show A10K2.u2505 = KTree.node A10K2.u2501 (nat_lit 42621047) (nat_lit 3770410593) (nat_lit 0) A10K2.u2504 from rfl, allE_node, arows2501, irow2505, arows2504]
  all_goals rfl

theorem atot2505 : totK PA10K2 A10K2.u2505 = [876513839775, 6782061820692, 15413812439503, 12139930258784, 2755123787178, 153818939853, 0, 0, 0, 0] := by
  rw [show A10K2.u2505 = KTree.node A10K2.u2501 (nat_lit 42621047) (nat_lit 3770410593) (nat_lit 0) A10K2.u2504 from rfl, totK_node, atot2501, atot2504]
  decide +kernel

theorem arows2513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2513 = true := by
  rw [show A10K2.u2513 = KTree.node A10K2.u2509 (nat_lit 42678463) (nat_lit 12294915860) (nat_lit 0) A10K2.u2512 from rfl, allE_node, arows2509, irow2513, arows2512]
  all_goals rfl

theorem atot2513 : totK PA10K2 A10K2.u2513 = [1609698614687, 8027145304391, 14675772041659, 11626106130960, 3546864072337, 366420811327, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2513 = KTree.node A10K2.u2509 (nat_lit 42678463) (nat_lit 12294915860) (nat_lit 0) A10K2.u2512 from rfl, totK_node, atot2509, atot2512]
  decide +kernel

theorem arows2520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2520 = true := by
  rw [show A10K2.u2520 = KTree.node A10K2.u2516 (nat_lit 42725361) (nat_lit 8022733026) (nat_lit 0) A10K2.u2519 from rfl, allE_node, arows2516, irow2520, arows2519]
  all_goals rfl

theorem atot2520 : totK PA10K2 A10K2.u2520 = [0, 2254063235632, 10551774966601, 16168503271597, 9207530217303, 1774416115754, 93891684850, 0, 0, 0] := by
  rw [show A10K2.u2520 = KTree.node A10K2.u2516 (nat_lit 42725361) (nat_lit 8022733026) (nat_lit 0) A10K2.u2519 from rfl, totK_node, atot2516, atot2519]
  decide +kernel

theorem arows2529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2529 = true := by
  rw [show A10K2.u2529 = KTree.node A10K2.u2525 (nat_lit 42822729) (nat_lit 6237501409) (nat_lit 0) A10K2.u2528 from rfl, allE_node, arows2525, irow2529, arows2528]
  all_goals rfl

theorem atot2529 : totK PA10K2 A10K2.u2529 = [0, 1436473895890, 7937152109018, 15207447684282, 11313560764716, 2927423777793, 254681195477, 9729745405, 0, 0] := by
  rw [show A10K2.u2529 = KTree.node A10K2.u2525 (nat_lit 42822729) (nat_lit 6237501409) (nat_lit 0) A10K2.u2528 from rfl, totK_node, atot2525, atot2528]
  decide +kernel

theorem arows2536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2536 = true := by
  rw [show A10K2.u2536 = KTree.node A10K2.u2532 (nat_lit 42855425) (nat_lit 7041414303) (nat_lit 0) A10K2.u2535 from rfl, allE_node, arows2532, irow2536, arows2535]
  all_goals rfl

theorem atot2536 : totK PA10K2 A10K2.u2536 = [0, 1306223671615, 6753015352909, 13095123840735, 11662296746930, 4515140929793, 675139554284, 21532950751, 0, 0] := by
  rw [show A10K2.u2536 = KTree.node A10K2.u2532 (nat_lit 42855425) (nat_lit 7041414303) (nat_lit 0) A10K2.u2535 from rfl, totK_node, atot2532, atot2535]
  decide +kernel

theorem arows2544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2544 = true := by
  rw [show A10K2.u2544 = KTree.node A10K2.u2540 (nat_lit 42883853) (nat_lit 5810952350) (nat_lit 0) A10K2.u2543 from rfl, allE_node, arows2540, irow2544, arows2543]
  all_goals rfl

theorem atot2544 : totK PA10K2 A10K2.u2544 = [0, 810058863673, 6572317598023, 15516012323791, 12194307673813, 2506570992144, 119815055139, 0, 0, 0] := by
  rw [show A10K2.u2544 = KTree.node A10K2.u2540 (nat_lit 42883853) (nat_lit 5810952350) (nat_lit 0) A10K2.u2543 from rfl, totK_node, atot2540, atot2543]
  decide +kernel

theorem arows2551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2551 = true := by
  rw [show A10K2.u2551 = KTree.node A10K2.u2547 (nat_lit 42941879) (nat_lit 15198214983) (nat_lit 0) A10K2.u2550 from rfl, allE_node, arows2547, irow2551, arows2550]
  all_goals rfl

theorem atot2551 : totK PA10K2 A10K2.u2551 = [444521281299, 3042673174323, 8887267043220, 13460707381054, 10336729659376, 3148008494132, 308316785676, 6239673734, 0, 0] := by
  rw [show A10K2.u2551 = KTree.node A10K2.u2547 (nat_lit 42941879) (nat_lit 15198214983) (nat_lit 0) A10K2.u2550 from rfl, totK_node, atot2547, atot2550]
  decide +kernel

theorem arows2564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2564 = true := by
  rw [show A10K2.u2564 = KTree.node A10K2.u2560 (nat_lit 43013278) (nat_lit 12358955946) (nat_lit 0) A10K2.u2563 from rfl, allE_node, arows2560, irow2564, arows2563]
  all_goals rfl

theorem atot2564 : totK PA10K2 A10K2.u2564 = [1351600117055, 7699899884540, 14658892735263, 10898701444843, 3187338930743, 434465951188, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u2564 = KTree.node A10K2.u2560 (nat_lit 43013278) (nat_lit 12358955946) (nat_lit 0) A10K2.u2563 from rfl, totK_node, atot2560, atot2563]
  decide +kernel

theorem arows2571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2571 = true := by
  rw [show A10K2.u2571 = KTree.node A10K2.u2567 (nat_lit 43067052) (nat_lit 11716372436) (nat_lit 0) A10K2.u2570 from rfl, allE_node, arows2567, irow2571, arows2570]
  all_goals rfl

theorem atot2571 : totK PA10K2 A10K2.u2571 = [1597535614651, 7374860439987, 13240458480566, 11461452696082, 4073439639342, 473154804110, 10957026886, 0, 0, 0] := by
  rw [show A10K2.u2571 = KTree.node A10K2.u2567 (nat_lit 43067052) (nat_lit 11716372436) (nat_lit 0) A10K2.u2570 from rfl, totK_node, atot2567, atot2570]
  decide +kernel

theorem arows2579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2579 = true := by
  rw [show A10K2.u2579 = KTree.node A10K2.u2575 (nat_lit 43100259) (nat_lit 5331477562) (nat_lit 0) A10K2.u2578 from rfl, allE_node, arows2575, irow2579, arows2578]
  all_goals rfl

theorem atot2579 : totK PA10K2 A10K2.u2579 = [502723522018, 5022149300414, 13734927604021, 13763631740143, 5157107176667, 703899030441, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u2579 = KTree.node A10K2.u2575 (nat_lit 43100259) (nat_lit 5331477562) (nat_lit 0) A10K2.u2578 from rfl, totK_node, atot2575, atot2578]
  decide +kernel

theorem arows2586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2586 = true := by
  rw [show A10K2.u2586 = KTree.node A10K2.u2582 (nat_lit 43128895) (nat_lit 9553549171) (nat_lit 0) A10K2.u2585 from rfl, allE_node, arows2582, irow2586, arows2585]
  all_goals rfl

theorem atot2586 : totK PA10K2 A10K2.u2586 = [1728443571431, 8181005475950, 14044072070250, 10498075812344, 3314931254225, 339945852859, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u2586 = KTree.node A10K2.u2582 (nat_lit 43128895) (nat_lit 9553549171) (nat_lit 0) A10K2.u2585 from rfl, totK_node, atot2582, atot2585]
  decide +kernel

theorem arows2595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2595 = true := by
  rw [show A10K2.u2595 = KTree.node A10K2.u2591 (nat_lit 43165119) (nat_lit 12084918189) (nat_lit 0) A10K2.u2594 from rfl, allE_node, arows2591, irow2595, arows2594]
  all_goals rfl

theorem atot2595 : totK PA10K2 A10K2.u2595 = [568096137437, 5346649280161, 13979017478453, 13372592344266, 4113130048939, 400522604772, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2595 = KTree.node A10K2.u2591 (nat_lit 43165119) (nat_lit 12084918189) (nat_lit 0) A10K2.u2594 from rfl, totK_node, atot2591, atot2594]
  decide +kernel

theorem arows2602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2602 = true := by
  rw [show A10K2.u2602 = KTree.node A10K2.u2598 (nat_lit 43272379) (nat_lit 5857048971) (nat_lit 0) A10K2.u2601 from rfl, allE_node, arows2598, irow2602, arows2601]
  all_goals rfl

theorem atot2602 : totK PA10K2 A10K2.u2602 = [0, 2518589909006, 11103064459617, 15676737200069, 7723877357950, 1197253790064, 44026197503, 0, 0, 0] := by
  rw [show A10K2.u2602 = KTree.node A10K2.u2598 (nat_lit 43272379) (nat_lit 5857048971) (nat_lit 0) A10K2.u2601 from rfl, totK_node, atot2598, atot2601]
  decide +kernel

theorem arows2610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2610 = true := by
  rw [show A10K2.u2610 = KTree.node A10K2.u2606 (nat_lit 43342372) (nat_lit 13617786596) (nat_lit 0) A10K2.u2609 from rfl, allE_node, arows2606, irow2610, arows2609]
  all_goals rfl

theorem atot2610 : totK PA10K2 A10K2.u2610 = [0, 1978154284293, 9729559123456, 15852696281568, 9151760168176, 1568424260719, 69384189482, 0, 0, 0] := by
  rw [show A10K2.u2610 = KTree.node A10K2.u2606 (nat_lit 43342372) (nat_lit 13617786596) (nat_lit 0) A10K2.u2609 from rfl, totK_node, atot2606, atot2609]
  decide +kernel

theorem arows2617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2617 = true := by
  rw [show A10K2.u2617 = KTree.node A10K2.u2613 (nat_lit 43402410) (nat_lit 12978655923) (nat_lit 0) A10K2.u2616 from rfl, allE_node, arows2613, irow2617, arows2616]
  all_goals rfl

theorem atot2617 : totK PA10K2 A10K2.u2617 = [0, 1595696682260, 8725148284544, 15685059312359, 9678466164476, 1734467033714, 93836009804, 0, 0, 0] := by
  rw [show A10K2.u2617 = KTree.node A10K2.u2613 (nat_lit 43402410) (nat_lit 12978655923) (nat_lit 0) A10K2.u2616 from rfl, totK_node, atot2613, atot2616]
  decide +kernel

theorem arows2627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2627 = true := by
  rw [show A10K2.u2627 = KTree.node A10K2.u2623 (nat_lit 44040960) (nat_lit 14955865490) (nat_lit 0) A10K2.u2626 from rfl, allE_node, arows2623, irow2627, arows2626]
  all_goals rfl

theorem atot2627 : totK PA10K2 A10K2.u2627 = [0, 1585054149079, 7720250526705, 13945225762952, 10835240464657, 3234567397397, 358422165524, 6354482628, 0, 0] := by
  rw [show A10K2.u2627 = KTree.node A10K2.u2623 (nat_lit 44040960) (nat_lit 14955865490) (nat_lit 0) A10K2.u2626 from rfl, totK_node, atot2623, atot2626]
  decide +kernel

theorem arows2634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2634 = true := by
  rw [show A10K2.u2634 = KTree.node A10K2.u2630 (nat_lit 44073534) (nat_lit 15149369558) (nat_lit 0) A10K2.u2633 from rfl, allE_node, arows2630, irow2634, arows2633]
  all_goals rfl

theorem atot2634 : totK PA10K2 A10K2.u2634 = [0, 593403324104, 5258535404693, 13774726376885, 13465265515634, 4771136374808, 659350623386, 30650496230, 0, 0] := by
  rw [show A10K2.u2634 = KTree.node A10K2.u2630 (nat_lit 44073534) (nat_lit 15149369558) (nat_lit 0) A10K2.u2633 from rfl, totK_node, atot2630, atot2633]
  decide +kernel

theorem arows2642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2642 = true := by
  rw [show A10K2.u2642 = KTree.node A10K2.u2638 (nat_lit 44175813) (nat_lit 5012263003) (nat_lit 0) A10K2.u2641 from rfl, allE_node, arows2638, irow2642, arows2641]
  all_goals rfl

theorem atot2642 : totK PA10K2 A10K2.u2642 = [0, 1838196942601, 8358975430651, 14061217163770, 10665974538103, 3250276207643, 311043194441, 5546304973, 0, 0] := by
  rw [show A10K2.u2642 = KTree.node A10K2.u2638 (nat_lit 44175813) (nat_lit 5012263003) (nat_lit 0) A10K2.u2641 from rfl, totK_node, atot2638, atot2641]
  decide +kernel

theorem arows2649 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2649 = true := by
  rw [show A10K2.u2649 = KTree.node A10K2.u2645 (nat_lit 44214195) (nat_lit 9405989294) (nat_lit 0) A10K2.u2648 from rfl, allE_node, arows2645, irow2649, arows2648]
  all_goals rfl

theorem atot2649 : totK PA10K2 A10K2.u2649 = [0, 786108072152, 5740419426036, 14046390859552, 12927402805482, 3879081227222, 393214209434, 6354482628, 0, 0] := by
  rw [show A10K2.u2649 = KTree.node A10K2.u2645 (nat_lit 44214195) (nat_lit 9405989294) (nat_lit 0) A10K2.u2648 from rfl, totK_node, atot2645, atot2648]
  decide +kernel

theorem arows2658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2658 = true := by
  rw [show A10K2.u2658 = KTree.node A10K2.u2654 (nat_lit 44650574) (nat_lit 4449224923) (nat_lit 0) A10K2.u2657 from rfl, allE_node, arows2654, irow2658, arows2657]
  all_goals rfl

theorem atot2658 : totK PA10K2 A10K2.u2658 = [0, 1816211868302, 9553554896870, 16203000749372, 9843878079617, 1848410226117, 80203123337, 0, 0, 0] := by
  rw [show A10K2.u2658 = KTree.node A10K2.u2654 (nat_lit 44650574) (nat_lit 4449224923) (nat_lit 0) A10K2.u2657 from rfl, totK_node, atot2654, atot2657]
  decide +kernel

theorem arows2665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2665 = true := by
  rw [show A10K2.u2665 = KTree.node A10K2.u2661 (nat_lit 44681572) (nat_lit 14004928648) (nat_lit 0) A10K2.u2664 from rfl, allE_node, arows2661, irow2665, arows2664]
  all_goals rfl

theorem atot2665 : totK PA10K2 A10K2.u2665 = [0, 516552094339, 4081708373435, 11790750700725, 14443719797724, 6420186969472, 913299743253, 37204059898, 0, 0] := by
  rw [show A10K2.u2665 = KTree.node A10K2.u2661 (nat_lit 44681572) (nat_lit 14004928648) (nat_lit 0) A10K2.u2664 from rfl, totK_node, atot2661, atot2664]
  decide +kernel

theorem arows2673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2673 = true := by
  rw [show A10K2.u2673 = KTree.node A10K2.u2669 (nat_lit 44712748) (nat_lit 13235443842) (nat_lit 0) A10K2.u2672 from rfl, allE_node, arows2669, irow2673, arows2672]
  all_goals rfl

theorem atot2673 : totK PA10K2 A10K2.u2673 = [0, 1599730440949, 8534860887234, 15397332723798, 10349454093869, 2107982710067, 106558736502, 0, 0, 0] := by
  rw [show A10K2.u2673 = KTree.node A10K2.u2669 (nat_lit 44712748) (nat_lit 13235443842) (nat_lit 0) A10K2.u2672 from rfl, totK_node, atot2669, atot2672]
  decide +kernel

theorem arows2680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2680 = true := by
  rw [show A10K2.u2680 = KTree.node A10K2.u2676 (nat_lit 44771006) (nat_lit 15268314887) (nat_lit 0) A10K2.u2679 from rfl, allE_node, arows2676, irow2680, arows2679]
  all_goals rfl

theorem atot2680 : totK PA10K2 A10K2.u2680 = [0, 1609698614687, 7915192092515, 14443470253673, 11437565303638, 3383601336035, 360790835526, 6354482628, 0, 0] := by
  rw [show A10K2.u2680 = KTree.node A10K2.u2676 (nat_lit 44771006) (nat_lit 15268314887) (nat_lit 0) A10K2.u2679 from rfl, totK_node, atot2676, atot2679]
  decide +kernel

theorem arows2691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2691 = true := by
  rw [show A10K2.u2691 = KTree.node A10K2.u2687 (nat_lit 44809366) (nat_lit 15320969996) (nat_lit 0) A10K2.u2690 from rfl, allE_node, arows2687, irow2691, arows2690]
  all_goals rfl

theorem atot2691 : totK PA10K2 A10K2.u2691 = [0, 761005751305, 5600595467610, 13987236237001, 14086072219354, 5009693092257, 483268715375, 7047025452, 0, 0] := by
  rw [show A10K2.u2691 = KTree.node A10K2.u2687 (nat_lit 44809366) (nat_lit 15320969996) (nat_lit 0) A10K2.u2690 from rfl, totK_node, atot2687, atot2690]
  decide +kernel

theorem arows2698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2698 = true := by
  rw [show A10K2.u2698 = KTree.node A10K2.u2694 (nat_lit 45117701) (nat_lit 6764150679) (nat_lit 0) A10K2.u2697 from rfl, allE_node, arows2694, irow2698, arows2697]
  all_goals rfl

theorem atot2698 : totK PA10K2 A10K2.u2698 = [0, 1045008235948, 6493424145254, 13983789018789, 12003809565390, 3877274761291, 523932690453, 30220878370, 0, 0] := by
  rw [show A10K2.u2698 = KTree.node A10K2.u2694 (nat_lit 45117701) (nat_lit 6764150679) (nat_lit 0) A10K2.u2697 from rfl, totK_node, atot2694, atot2697]
  decide +kernel

theorem arows2706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2706 = true := by
  rw [show A10K2.u2706 = KTree.node A10K2.u2702 (nat_lit 45168092) (nat_lit 5503332563) (nat_lit 0) A10K2.u2705 from rfl, allE_node, arows2702, irow2706, arows2705]
  all_goals rfl

theorem atot2706 : totK PA10K2 A10K2.u2706 = [0, 1879388034473, 8688864684326, 14500077840992, 10221507352083, 2733698848757, 251678572969, 5546304973, 0, 0] := by
  rw [show A10K2.u2706 = KTree.node A10K2.u2702 (nat_lit 45168092) (nat_lit 5503332563) (nat_lit 0) A10K2.u2705 from rfl, totK_node, atot2702, atot2705]
  decide +kernel

theorem arows2713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2713 = true := by
  rw [show A10K2.u2713 = KTree.node A10K2.u2709 (nat_lit 45201750) (nat_lit 9720423212) (nat_lit 0) A10K2.u2712 from rfl, allE_node, arows2709, irow2713, arows2712]
  all_goals rfl

theorem atot2713 : totK PA10K2 A10K2.u2713 = [0, 380254228052, 4059061306518, 12812778769169, 14930486729568, 5841589732280, 775552957419, 36768997705, 0, 0] := by
  rw [show A10K2.u2713 = KTree.node A10K2.u2709 (nat_lit 45201750) (nat_lit 9720423212) (nat_lit 0) A10K2.u2712 from rfl, totK_node, atot2709, atot2712]
  decide +kernel

theorem arows2722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2722 = true := by
  rw [show A10K2.u2722 = KTree.node A10K2.u2718 (nat_lit 45232023) (nat_lit 12677292857) (nat_lit 0) A10K2.u2721 from rfl, allE_node, arows2718, irow2722, arows2721]
  all_goals rfl

theorem atot2722 : totK PA10K2 A10K2.u2722 = [0, 2129015206400, 10252884443903, 15751681390757, 8243183664858, 1275366303159, 62600422739, 0, 0, 0] := by
  rw [show A10K2.u2722 = KTree.node A10K2.u2718 (nat_lit 45232023) (nat_lit 12677292857) (nat_lit 0) A10K2.u2721 from rfl, totK_node, atot2718, atot2721]
  decide +kernel

theorem arows2729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2729 = true := by
  rw [show A10K2.u2729 = KTree.node A10K2.u2725 (nat_lit 45270698) (nat_lit 12800291610) (nat_lit 0) A10K2.u2728 from rfl, allE_node, arows2725, irow2729, arows2728]
  all_goals rfl

theorem atot2729 : totK PA10K2 A10K2.u2729 = [0, 0, 3039817240378, 12545000959803, 15572215731062, 5665959665488, 716144414195, 31296045761, 0, 0] := by
  rw [show A10K2.u2729 = KTree.node A10K2.u2725 (nat_lit 45270698) (nat_lit 12800291610) (nat_lit 0) A10K2.u2728 from rfl, totK_node, atot2725, atot2728]
  decide +kernel

theorem arows2737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2737 = true := by
  rw [show A10K2.u2737 = KTree.node A10K2.u2733 (nat_lit 45426024) (nat_lit 8239821958) (nat_lit 0) A10K2.u2736 from rfl, allE_node, arows2733, irow2737, arows2736]
  all_goals rfl

theorem atot2737 : totK PA10K2 A10K2.u2737 = [0, 0, 2628484261053, 11257264082731, 15599237176497, 7323187710842, 1068839902184, 42819180159, 0, 0] := by
  rw [show A10K2.u2737 = KTree.node A10K2.u2733 (nat_lit 45426024) (nat_lit 8239821958) (nat_lit 0) A10K2.u2736 from rfl, totK_node, atot2733, atot2736]
  decide +kernel

theorem arows2744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2744 = true := by
  rw [show A10K2.u2744 = KTree.node A10K2.u2740 (nat_lit 45486646) (nat_lit 12806849229) (nat_lit 0) A10K2.u2743 from rfl, allE_node, arows2740, irow2744, arows2743]
  all_goals rfl

theorem atot2744 : totK PA10K2 A10K2.u2744 = [0, 0, 2204138249792, 10357114976136, 15748297823020, 7824745154191, 1305854870903, 67432810860, 0, 0] := by
  rw [show A10K2.u2744 = KTree.node A10K2.u2740 (nat_lit 45486646) (nat_lit 12806849229) (nat_lit 0) A10K2.u2743 from rfl, totK_node, atot2740, atot2743]
  decide +kernel

theorem arows2754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2754 = true := by
  rw [show A10K2.u2754 = KTree.node A10K2.u2750 (nat_lit 45524773) (nat_lit 7311967796) (nat_lit 0) A10K2.u2753 from rfl, allE_node, arows2750, irow2754, arows2753]
  all_goals rfl

theorem atot2754 : totK PA10K2 A10K2.u2754 = [317619887890, 1050935918641, 1642914656699, 5531557956927, 13114731259994, 11315557824640, 3525851668675, 384962563863, 6354482628, 0] := by
  rw [show A10K2.u2754 = KTree.node A10K2.u2750 (nat_lit 45524773) (nat_lit 7311967796) (nat_lit 0) A10K2.u2753 from rfl, totK_node, atot2750, atot2753]
  decide +kernel

theorem arows2761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2761 = true := by
  rw [show A10K2.u2761 = KTree.node A10K2.u2757 (nat_lit 46159917) (nat_lit 6564379686) (nat_lit 0) A10K2.u2760 from rfl, allE_node, arows2757, irow2761, arows2760]
  all_goals rfl

theorem atot2761 : totK PA10K2 A10K2.u2761 = [1888237035188, 9531251317342, 15979480426654, 9886824292623, 1988852329874, 100101167484, 0, 0, 0, 0] := by
  rw [show A10K2.u2761 = KTree.node A10K2.u2757 (nat_lit 46159917) (nat_lit 6564379686) (nat_lit 0) A10K2.u2760 from rfl, totK_node, atot2757, atot2760]
  decide +kernel

theorem arows2769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2769 = true := by
  rw [show A10K2.u2769 = KTree.node A10K2.u2765 (nat_lit 46190976) (nat_lit 15375577360) (nat_lit 0) A10K2.u2768 from rfl, allE_node, arows2765, irow2769, arows2768]
  all_goals rfl

theorem atot2769 : totK PA10K2 A10K2.u2769 = [783941292525, 4996290117144, 12330539422774, 13792829408587, 6014831866494, 877252064925, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u2769 = KTree.node A10K2.u2765 (nat_lit 46190976) (nat_lit 15375577360) (nat_lit 0) A10K2.u2768 from rfl, totK_node, atot2765, atot2768]
  decide +kernel

theorem arows2776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2776 = true := by
  rw [show A10K2.u2776 = KTree.node A10K2.u2772 (nat_lit 46360221) (nat_lit 5384839567) (nat_lit 0) A10K2.u2775 from rfl, allE_node, arows2772, irow2776, arows2775]
  all_goals rfl

theorem atot2776 : totK PA10K2 A10K2.u2776 = [1461308260998, 8156005540649, 15775014918260, 11720081858612, 2784281109871, 157265067211, 0, 0, 0, 0] := by
  rw [show A10K2.u2776 = KTree.node A10K2.u2772 (nat_lit 46360221) (nat_lit 5384839567) (nat_lit 0) A10K2.u2775 from rfl, totK_node, atot2772, atot2775]
  decide +kernel

theorem arows2785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2785 = true := by
  rw [show A10K2.u2785 = KTree.node A10K2.u2781 (nat_lit 46392554) (nat_lit 12196253485) (nat_lit 0) A10K2.u2784 from rfl, allE_node, arows2781, irow2785, arows2784]
  all_goals rfl

theorem atot2785 : totK PA10K2 A10K2.u2785 = [0, 2160891832953, 10119499697054, 16101698529711, 9510824440639, 1706900568434, 75062079822, 0, 0, 0] := by
  rw [show A10K2.u2785 = KTree.node A10K2.u2781 (nat_lit 46392554) (nat_lit 12196253485) (nat_lit 0) A10K2.u2784 from rfl, totK_node, atot2781, atot2784]
  decide +kernel

theorem arows2792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2792 = true := by
  rw [show A10K2.u2792 = KTree.node A10K2.u2788 (nat_lit 46424460) (nat_lit 8428568161) (nat_lit 0) A10K2.u2791 from rfl, allE_node, arows2788, irow2792, arows2791]
  all_goals rfl

theorem atot2792 : totK PA10K2 A10K2.u2792 = [0, 1504437600655, 8620755676410, 16086924223543, 10637710230237, 2082262467695, 102790279195, 0, 0, 0] := by
  rw [show A10K2.u2792 = KTree.node A10K2.u2788 (nat_lit 46424460) (nat_lit 8428568161) (nat_lit 0) A10K2.u2791 from rfl, totK_node, atot2788, atot2791]
  decide +kernel

theorem arows2800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2800 = true := by
  rw [show A10K2.u2800 = KTree.node A10K2.u2796 (nat_lit 46457414) (nat_lit 13415364663) (nat_lit 0) A10K2.u2799 from rfl, allE_node, arows2796, irow2800, arows2799]
  all_goals rfl

theorem atot2800 : totK PA10K2 A10K2.u2800 = [0, 1071203765815, 5990332561189, 12783255104127, 12627426714896, 5297634604457, 830351580572, 36134558889, 0, 0] := by
  rw [show A10K2.u2800 = KTree.node A10K2.u2796 (nat_lit 46457414) (nat_lit 13415364663) (nat_lit 0) A10K2.u2799 from rfl, totK_node, atot2796, atot2799]
  decide +kernel

theorem arows2807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2807 = true := by
  rw [show A10K2.u2807 = KTree.node A10K2.u2803 (nat_lit 46625950) (nat_lit 14941068844) (nat_lit 0) A10K2.u2806 from rfl, allE_node, arows2803, irow2807, arows2806]
  all_goals rfl

theorem atot2807 : totK PA10K2 A10K2.u2807 = [861896674927, 4924671909622, 11473389507218, 13577513436266, 7456015404910, 1435405674108, 69519743899, 0, 0, 0] := by
  rw [show A10K2.u2807 = KTree.node A10K2.u2803 (nat_lit 46625950) (nat_lit 14941068844) (nat_lit 0) A10K2.u2806 from rfl, totK_node, atot2803, atot2806]
  decide +kernel

theorem arows2819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2819 = true := by
  rw [show A10K2.u2819 = KTree.node A10K2.u2815 (nat_lit 46755575) (nat_lit 14516957277) (nat_lit 0) A10K2.u2818 from rfl, allE_node, arows2815, irow2819, arows2818]
  all_goals rfl

theorem atot2819 : totK PA10K2 A10K2.u2819 = [1443757010989, 7854605670426, 14874207942990, 11351834417729, 3422731475369, 449159714106, 20331139758, 0, 0, 0] := by
  rw [show A10K2.u2819 = KTree.node A10K2.u2815 (nat_lit 46755575) (nat_lit 14516957277) (nat_lit 0) A10K2.u2818 from rfl, totK_node, atot2815, atot2818]
  decide +kernel

theorem arows2826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2826 = true := by
  rw [show A10K2.u2826 = KTree.node A10K2.u2822 (nat_lit 46787681) (nat_lit 6270376452) (nat_lit 0) A10K2.u2825 from rfl, allE_node, arows2822, irow2826, arows2825]
  all_goals rfl

theorem atot2826 : totK PA10K2 A10K2.u2826 = [1079427622363, 5985273001723, 13070527455814, 13107187641554, 5154477083039, 585371945180, 11638555097, 0, 0, 0] := by
  rw [show A10K2.u2826 = KTree.node A10K2.u2822 (nat_lit 46787681) (nat_lit 6270376452) (nat_lit 0) A10K2.u2825 from rfl, totK_node, atot2822, atot2825]
  decide +kernel

theorem arows2834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2834 = true := by
  rw [show A10K2.u2834 = KTree.node A10K2.u2830 (nat_lit 46843034) (nat_lit 15154852766) (nat_lit 0) A10K2.u2833 from rfl, allE_node, arows2830, irow2834, arows2833]
  all_goals rfl

theorem atot2834 : totK PA10K2 A10K2.u2834 = [1015766685030, 6724936312800, 14569410365971, 12240306623325, 3666099814341, 381202734122, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2834 = KTree.node A10K2.u2830 (nat_lit 46843034) (nat_lit 15154852766) (nat_lit 0) A10K2.u2833 from rfl, totK_node, atot2830, atot2833]
  decide +kernel

theorem arows2841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2841 = true := by
  rw [show A10K2.u2841 = KTree.node A10K2.u2837 (nat_lit 46884709) (nat_lit 6216669326) (nat_lit 0) A10K2.u2840 from rfl, allE_node, arows2837, irow2841, arows2840]
  all_goals rfl

theorem atot2841 : totK PA10K2 A10K2.u2841 = [1666676564852, 8337744915910, 15011098500535, 11347568516059, 3214350656994, 254643616711, 0, 0, 0, 0] := by
  rw [show A10K2.u2841 = KTree.node A10K2.u2837 (nat_lit 46884709) (nat_lit 6216669326) (nat_lit 0) A10K2.u2840 from rfl, totK_node, atot2837, atot2840]
  decide +kernel

theorem arows2850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2850 = true := by
  rw [show A10K2.u2850 = KTree.node A10K2.u2846 (nat_lit 46917341) (nat_lit 3220243777) (nat_lit 0) A10K2.u2849 from rfl, allE_node, arows2846, irow2850, arows2849]
  all_goals rfl

theorem atot2850 : totK PA10K2 A10K2.u2850 = [0, 2527231550593, 10990636729662, 15807625150876, 8596028513901, 1556291338217, 75062079822, 0, 0, 0] := by
  rw [show A10K2.u2850 = KTree.node A10K2.u2846 (nat_lit 46917341) (nat_lit 3220243777) (nat_lit 0) A10K2.u2849 from rfl, totK_node, atot2846, atot2849]
  decide +kernel

theorem arows2857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2857 = true := by
  rw [show A10K2.u2857 = KTree.node A10K2.u2853 (nat_lit 47014299) (nat_lit 9096502837) (nat_lit 0) A10K2.u2856 from rfl, allE_node, arows2853, irow2857, arows2856]
  all_goals rfl

theorem atot2857 : totK PA10K2 A10K2.u2857 = [0, 1442288790785, 8361032079504, 16081081593123, 10985247461146, 2191091427524, 105550031923, 0, 0, 0] := by
  rw [show A10K2.u2857 = KTree.node A10K2.u2853 (nat_lit 47014299) (nat_lit 9096502837) (nat_lit 0) A10K2.u2856 from rfl, totK_node, atot2853, atot2856]
  decide +kernel

theorem arows2865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2865 = true := by
  rw [show A10K2.u2865 = KTree.node A10K2.u2861 (nat_lit 47045165) (nat_lit 6147701679) (nat_lit 0) A10K2.u2864 from rfl, allE_node, arows2861, irow2865, arows2864]
  all_goals rfl

theorem atot2865 : totK PA10K2 A10K2.u2865 = [0, 796027745624, 5205590332430, 12563681871251, 13397871322348, 5789870755280, 870279291529, 36704093874, 0, 0] := by
  rw [show A10K2.u2865 = KTree.node A10K2.u2861 (nat_lit 47045165) (nat_lit 6147701679) (nat_lit 0) A10K2.u2864 from rfl, totK_node, atot2861, atot2864]
  decide +kernel

theorem arows2872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2872 = true := by
  rw [show A10K2.u2872 = KTree.node A10K2.u2868 (nat_lit 47098654) (nat_lit 7967096080) (nat_lit 0) A10K2.u2871 from rfl, allE_node, arows2868, irow2872, arows2871]
  all_goals rfl

theorem atot2872 : totK PA10K2 A10K2.u2872 = [0, 1298699626799, 7227697436486, 14440205633375, 11821797963964, 3294966019442, 297220993004, 6239673734, 0, 0] := by
  rw [show A10K2.u2872 = KTree.node A10K2.u2868 (nat_lit 47098654) (nat_lit 7967096080) (nat_lit 0) A10K2.u2871 from rfl, totK_node, atot2868, atot2871]
  decide +kernel

theorem arows2882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2882 = true := by
  rw [show A10K2.u2882 = KTree.node A10K2.u2878 (nat_lit 47145473) (nat_lit 10563061234) (nat_lit 0) A10K2.u2881 from rfl, allE_node, arows2878, irow2882, arows2881]
  all_goals rfl

theorem atot2882 : totK PA10K2 A10K2.u2882 = [480657707117, 3241020605488, 9800308191317, 14670376139997, 9364122517109, 1973066767268, 100675502142, 0, 0, 0] := by
  rw [show A10K2.u2882 = KTree.node A10K2.u2878 (nat_lit 47145473) (nat_lit 10563061234) (nat_lit 0) A10K2.u2881 from rfl, totK_node, atot2878, atot2881]
  decide +kernel

theorem arows2889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2889 = true := by
  rw [show A10K2.u2889 = KTree.node A10K2.u2885 (nat_lit 47738014) (nat_lit 15266959024) (nat_lit 0) A10K2.u2888 from rfl, allE_node, arows2885, irow2889, arows2888]
  all_goals rfl

theorem atot2889 : totK PA10K2 A10K2.u2889 = [1390061476929, 7922482160731, 15560679132671, 11818618178027, 2951820532896, 180022984552, 0, 0, 0, 0] := by
  rw [show A10K2.u2889 = KTree.node A10K2.u2885 (nat_lit 47738014) (nat_lit 15266959024) (nat_lit 0) A10K2.u2888 from rfl, totK_node, atot2885, atot2888]
  decide +kernel

theorem arows2897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2897 = true := by
  rw [show A10K2.u2897 = KTree.node A10K2.u2893 (nat_lit 47785884) (nat_lit 8864228820) (nat_lit 0) A10K2.u2896 from rfl, allE_node, arows2893, irow2897, arows2896]
  all_goals rfl

theorem atot2897 : totK PA10K2 A10K2.u2897 = [1304072599280, 7163367406476, 14022831740689, 11828260141665, 4266904135147, 637187739713, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u2897 = KTree.node A10K2.u2893 (nat_lit 47785884) (nat_lit 8864228820) (nat_lit 0) A10K2.u2896 from rfl, totK_node, atot2893, atot2896]
  decide +kernel

theorem arows2904 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2904 = true := by
  rw [show A10K2.u2904 = KTree.node A10K2.u2900 (nat_lit 47818683) (nat_lit 7045562274) (nat_lit 0) A10K2.u2903 from rfl, allE_node, arows2900, irow2904, arows2903]
  all_goals rfl

theorem atot2904 : totK PA10K2 A10K2.u2904 = [829662196464, 5268541279441, 12672167408216, 13744600339343, 5985954613867, 888765655755, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2904 = KTree.node A10K2.u2900 (nat_lit 47818683) (nat_lit 7045562274) (nat_lit 0) A10K2.u2903 from rfl, totK_node, atot2900, atot2903]
  decide +kernel

theorem arows2913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2913 = true := by
  rw [show A10K2.u2913 = KTree.node A10K2.u2909 (nat_lit 47913990) (nat_lit 15264674383) (nat_lit 0) A10K2.u2912 from rfl, allE_node, arows2909, irow2913, arows2912]
  all_goals rfl

theorem atot2913 : totK PA10K2 A10K2.u2913 = [2056796891622, 9447183550981, 15381559775895, 10040815364883, 2296670464489, 139115852206, 0, 0, 0, 0] := by
  rw [show A10K2.u2913 = KTree.node A10K2.u2909 (nat_lit 47913990) (nat_lit 15264674383) (nat_lit 0) A10K2.u2912 from rfl, totK_node, atot2909, atot2912]
  decide +kernel

theorem arows2920 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2920 = true := by
  rw [show A10K2.u2920 = KTree.node A10K2.u2916 (nat_lit 47943240) (nat_lit 13587039416) (nat_lit 0) A10K2.u2919 from rfl, allE_node, arows2916, irow2920, arows2919]
  all_goals rfl

theorem atot2920 : totK PA10K2 A10K2.u2920 = [332208314330, 4080797399160, 12756614564375, 15004507779106, 6421617008607, 780796632876, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u2920 = KTree.node A10K2.u2916 (nat_lit 47943240) (nat_lit 13587039416) (nat_lit 0) A10K2.u2919 from rfl, totK_node, atot2916, atot2919]
  decide +kernel

theorem arows2928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2928 = true := by
  rw [show A10K2.u2928 = KTree.node A10K2.u2924 (nat_lit 47974432) (nat_lit 13959179896) (nat_lit 0) A10K2.u2927 from rfl, allE_node, arows2924, irow2928, arows2927]
  all_goals rfl

theorem atot2928 : totK PA10K2 A10K2.u2928 = [0, 2276173887339, 10463613393359, 15950426684275, 8982862595775, 1695554773914, 91890566284, 0, 0, 0] := by
  rw [show A10K2.u2928 = KTree.node A10K2.u2924 (nat_lit 47974432) (nat_lit 13959179896) (nat_lit 0) A10K2.u2927 from rfl, totK_node, atot2924, atot2927]
  decide +kernel

theorem arows2935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2935 = true := by
  rw [show A10K2.u2935 = KTree.node A10K2.u2931 (nat_lit 48009478) (nat_lit 11404588832) (nat_lit 0) A10K2.u2934 from rfl, allE_node, arows2931, irow2935, arows2934]
  all_goals rfl

theorem atot2935 : totK PA10K2 A10K2.u2935 = [0, 846151510337, 5787507893345, 14039219568603, 13809125117590, 4695365098491, 464852166311, 7007974415, 0, 0] := by
  rw [show A10K2.u2935 = KTree.node A10K2.u2931 (nat_lit 48009478) (nat_lit 11404588832) (nat_lit 0) A10K2.u2934 from rfl, totK_node, atot2931, atot2934]
  decide +kernel

theorem arows2946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2946 = true := by
  rw [show A10K2.u2946 = KTree.node A10K2.u2942 (nat_lit 48063409) (nat_lit 9034755717) (nat_lit 0) A10K2.u2945 from rfl, allE_node, arows2942, irow2946, arows2945]
  all_goals rfl

theorem atot2946 : totK PA10K2 A10K2.u2946 = [0, 1606495829258, 8617784100376, 15836012263831, 11067932016217, 2446676397665, 131652681262, 0, 0, 0] := by
  rw [show A10K2.u2946 = KTree.node A10K2.u2942 (nat_lit 48063409) (nat_lit 9034755717) (nat_lit 0) A10K2.u2945 from rfl, totK_node, atot2942, atot2945]
  decide +kernel

theorem arows2953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2953 = true := by
  rw [show A10K2.u2953 = KTree.node A10K2.u2949 (nat_lit 48169038) (nat_lit 10892379551) (nat_lit 0) A10K2.u2952 from rfl, allE_node, arows2949, irow2953, arows2952]
  all_goals rfl

theorem atot2953 : totK PA10K2 A10K2.u2953 = [0, 1494678044789, 7670259886427, 14279313282105, 11678688840981, 3844039433640, 391108511672, 7151180950, 0, 0] := by
  rw [show A10K2.u2953 = KTree.node A10K2.u2949 (nat_lit 48169038) (nat_lit 10892379551) (nat_lit 0) A10K2.u2952 from rfl, totK_node, atot2949, atot2952]
  decide +kernel

theorem arows2961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2961 = true := by
  rw [show A10K2.u2961 = KTree.node A10K2.u2957 (nat_lit 48199336) (nat_lit 1555736759) (nat_lit 0) A10K2.u2960 from rfl, allE_node, arows2957, irow2961, arows2960]
  all_goals rfl

theorem atot2961 : totK PA10K2 A10K2.u2961 = [0, 891342416461, 6157751234091, 14357315260423, 13355776888606, 4270423348916, 371921640558, 6318667960, 0, 0] := by
  rw [show A10K2.u2961 = KTree.node A10K2.u2957 (nat_lit 48199336) (nat_lit 1555736759) (nat_lit 0) A10K2.u2960 from rfl, totK_node, atot2957, atot2960]
  decide +kernel

theorem arows2968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2968 = true := by
  rw [show A10K2.u2968 = KTree.node A10K2.u2964 (nat_lit 48231589) (nat_lit 3320028554) (nat_lit 0) A10K2.u2967 from rfl, allE_node, arows2964, irow2968, arows2967]
  all_goals rfl

theorem atot2968 : totK PA10K2 A10K2.u2968 = [0, 844719840339, 4951374049848, 11700606459317, 13299853937465, 6946928619217, 1291282049253, 67457817768, 0, 0] := by
  rw [show A10K2.u2968 = KTree.node A10K2.u2964 (nat_lit 48231589) (nat_lit 3320028554) (nat_lit 0) A10K2.u2967 from rfl, totK_node, atot2964, atot2967]
  decide +kernel

theorem arows2977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2977 = true := by
  rw [show A10K2.u2977 = KTree.node A10K2.u2973 (nat_lit 48263558) (nat_lit 15746881228) (nat_lit 0) A10K2.u2976 from rfl, allE_node, arows2973, irow2977, arows2976]
  all_goals rfl

theorem atot2977 : totK PA10K2 A10K2.u2977 = [0, 1361137082739, 7359460330449, 14294258999535, 11680348571568, 3895545120010, 524424523240, 25239774317, 0, 0] := by
  rw [show A10K2.u2977 = KTree.node A10K2.u2973 (nat_lit 48263558) (nat_lit 15746881228) (nat_lit 0) A10K2.u2976 from rfl, totK_node, atot2973, atot2976]
  decide +kernel

theorem arows2984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2984 = true := by
  rw [show A10K2.u2984 = KTree.node A10K2.u2980 (nat_lit 48431402) (nat_lit 3930251715) (nat_lit 0) A10K2.u2983 from rfl, allE_node, arows2980, irow2984, arows2983]
  all_goals rfl

theorem atot2984 : totK PA10K2 A10K2.u2984 = [0, 1378512023993, 7306140731261, 14221850875677, 11979686039761, 3965567751464, 450231171243, 10957026886, 0, 0] := by
  rw [show A10K2.u2984 = KTree.node A10K2.u2980 (nat_lit 48431402) (nat_lit 3930251715) (nat_lit 0) A10K2.u2983 from rfl, totK_node, atot2980, atot2983]
  decide +kernel

theorem arows2992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2992 = true := by
  rw [show A10K2.u2992 = KTree.node A10K2.u2988 (nat_lit 48463438) (nat_lit 10774798059) (nat_lit 0) A10K2.u2991 from rfl, allE_node, arows2988, irow2992, arows2991]
  all_goals rfl

theorem atot2992 : totK PA10K2 A10K2.u2992 = [0, 866737529530, 5907639789071, 14090420127485, 13726837221321, 4845244539165, 468363249521, 6904928264, 0, 0] := by
  rw [show A10K2.u2992 = KTree.node A10K2.u2988 (nat_lit 48463438) (nat_lit 10774798059) (nat_lit 0) A10K2.u2991 from rfl, totK_node, atot2988, atot2991]
  decide +kernel

theorem arows2999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2999 = true := by
  rw [show A10K2.u2999 = KTree.node A10K2.u2995 (nat_lit 48496084) (nat_lit 6438474807) (nat_lit 0) A10K2.u2998 from rfl, allE_node, arows2995, irow2999, arows2998]
  all_goals rfl

theorem atot2999 : totK PA10K2 A10K2.u2999 = [0, 0, 2002576352822, 9621389264371, 15747732735091, 9774086603810, 1893076792718, 98708155394, 0, 0] := by
  rw [show A10K2.u2999 = KTree.node A10K2.u2995 (nat_lit 48496084) (nat_lit 6438474807) (nat_lit 0) A10K2.u2998 from rfl, totK_node, atot2995, atot2998]
  decide +kernel

theorem arows3009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3009 = true := by
  rw [show A10K2.u3009 = KTree.node A10K2.u3005 (nat_lit 48528819) (nat_lit 9277487096) (nat_lit 0) A10K2.u3008 from rfl, allE_node, arows3005, irow3009, arows3008]
  all_goals rfl

theorem atot3009 : totK PA10K2 A10K2.u3009 = [0, 0, 1069217766283, 6728646503676, 14546627194842, 12255660425048, 3695170565542, 387470426089, 7237400819, 0] := by
  rw [show A10K2.u3009 = KTree.node A10K2.u3005 (nat_lit 48528819) (nat_lit 9277487096) (nat_lit 0) A10K2.u3008 from rfl, totK_node, atot3005, atot3008]
  decide +kernel

theorem arows3016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3016 = true := by
  rw [show A10K2.u3016 = KTree.node A10K2.u3012 (nat_lit 48700830) (nat_lit 15479214158) (nat_lit 0) A10K2.u3015 from rfl, allE_node, arows3012, irow3016, arows3015]
  all_goals rfl

theorem atot3016 : totK PA10K2 A10K2.u3016 = [0, 0, 2244972050941, 10501400303827, 16239663095881, 9227522729146, 1576840294332, 66637137704, 0, 0] := by
  rw [show A10K2.u3016 = KTree.node A10K2.u3012 (nat_lit 48700830) (nat_lit 15479214158) (nat_lit 0) A10K2.u3015 from rfl, totK_node, atot3012, atot3015]
  decide +kernel

theorem arows3024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3024 = true := by
  rw [show A10K2.u3024 = KTree.node A10K2.u3020 (nat_lit 48838810) (nat_lit 14975758804) (nat_lit 0) A10K2.u3023 from rfl, allE_node, arows3020, irow3024, arows3023]
  all_goals rfl

theorem atot3024 : totK PA10K2 A10K2.u3024 = [0, 2169420268965, 9148962800522, 13540525307690, 9160944936221, 4091777238815, 974018894832, 62368562949, 0, 0] := by
  rw [show A10K2.u3024 = KTree.node A10K2.u3020 (nat_lit 48838810) (nat_lit 14975758804) (nat_lit 0) A10K2.u3023 from rfl, totK_node, atot3020, atot3023]
  decide +kernel

theorem arows3031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3031 = true := by
  rw [show A10K2.u3031 = KTree.node A10K2.u3027 (nat_lit 48870683) (nat_lit 10054382329) (nat_lit 0) A10K2.u3030 from rfl, allE_node, arows3027, irow3031, arows3030]
  all_goals rfl

theorem atot3031 : totK PA10K2 A10K2.u3031 = [0, 119627100822, 3584261071085, 12556965841813, 15231232967114, 6493419764406, 904717247498, 36968589557, 0, 0] := by
  rw [show A10K2.u3031 = KTree.node A10K2.u3027 (nat_lit 48870683) (nat_lit 10054382329) (nat_lit 0) A10K2.u3030 from rfl, totK_node, atot3027, atot3030]
  decide +kernel

theorem arows3040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3040 = true := by
  rw [show A10K2.u3040 = KTree.node A10K2.u3036 (nat_lit 48906501) (nat_lit 6941659939) (nat_lit 0) A10K2.u3039 from rfl, allE_node, arows3036, irow3040, arows3039]
  all_goals rfl

theorem atot3040 : totK PA10K2 A10K2.u3040 = [0, 1538572446206, 8326357240883, 15447859741276, 11092215231265, 2616047003388, 153594299197, 0, 0, 0] := by
  rw [show A10K2.u3040 = KTree.node A10K2.u3036 (nat_lit 48906501) (nat_lit 6941659939) (nat_lit 0) A10K2.u3039 from rfl, totK_node, atot3036, atot3039]
  decide +kernel

theorem arows3047 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3047 = true := by
  rw [show A10K2.u3047 = KTree.node A10K2.u3043 (nat_lit 48960440) (nat_lit 13609920443) (nat_lit 0) A10K2.u3046 from rfl, allE_node, arows3043, irow3047, arows3046]
  all_goals rfl

theorem atot3047 : totK PA10K2 A10K2.u3047 = [0, 1850913501927, 8509869588124, 14475917640834, 10760132244030, 3034782221403, 289535373946, 6354482628, 0, 0] := by
  rw [show A10K2.u3047 = KTree.node A10K2.u3043 (nat_lit 48960440) (nat_lit 13609920443) (nat_lit 0) A10K2.u3046 from rfl, totK_node, atot3043, atot3046]
  decide +kernel

theorem arows3055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3055 = true := by
  rw [show A10K2.u3055 = KTree.node A10K2.u3051 (nat_lit 48992332) (nat_lit 10115945838) (nat_lit 0) A10K2.u3054 from rfl, allE_node, arows3051, irow3055, arows3054]
  all_goals rfl

theorem atot3055 : totK PA10K2 A10K2.u3055 = [0, 359360087617, 4294978007088, 13038838347548, 14979178545963, 6338814551855, 728579222846, 13679205470, 0, 0] := by
  rw [show A10K2.u3055 = KTree.node A10K2.u3051 (nat_lit 48992332) (nat_lit 10115945838) (nat_lit 0) A10K2.u3054 from rfl, totK_node, atot3051, atot3054]
  decide +kernel

theorem arows3062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3062 = true := by
  rw [show A10K2.u3062 = KTree.node A10K2.u3058 (nat_lit 49097904) (nat_lit 10714244178) (nat_lit 0) A10K2.u3061 from rfl, allE_node, arows3058, irow3062, arows3061]
  all_goals rfl

theorem atot3062 : totK PA10K2 A10K2.u3062 = [0, 0, 1984454262763, 9653407306262, 15702688039851, 9542631811963, 1846664224640, 98635968377, 0, 0] := by
  rw [show A10K2.u3062 = KTree.node A10K2.u3058 (nat_lit 49097904) (nat_lit 10714244178) (nat_lit 0) A10K2.u3061 from rfl, totK_node, atot3058, atot3061]
  decide +kernel

theorem arows3076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3076 = true := by
  rw [show A10K2.u3076 = KTree.node A10K2.u3072 (nat_lit 49129834) (nat_lit 9865715108) (nat_lit 0) A10K2.u3075 from rfl, allE_node, arows3072, irow3076, arows3075]
  all_goals rfl

theorem atot3076 : totK PA10K2 A10K2.u3076 = [0, 0, 776975258324, 5988475150669, 14693513662119, 13417473341011, 4114288816500, 402017526790, 7380853412, 0] := by
  rw [show A10K2.u3076 = KTree.node A10K2.u3072 (nat_lit 49129834) (nat_lit 9865715108) (nat_lit 0) A10K2.u3075 from rfl, totK_node, atot3072, atot3075]
  decide +kernel

theorem arows3083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3083 = true := by
  rw [show A10K2.u3083 = KTree.node A10K2.u3079 (nat_lit 49174869) (nat_lit 6970753704) (nat_lit 0) A10K2.u3082 from rfl, allE_node, arows3079, irow3083, arows3082]
  all_goals rfl

theorem atot3083 : totK PA10K2 A10K2.u3083 = [0, 0, 2895222830943, 12051635047631, 15969134338255, 7141299768198, 1006846584641, 44356063129, 0, 0] := by
  rw [show A10K2.u3083 = KTree.node A10K2.u3079 (nat_lit 49174869) (nat_lit 6970753704) (nat_lit 0) A10K2.u3082 from rfl, totK_node, atot3079, atot3082]
  decide +kernel

theorem arows3091 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3091 = true := by
  rw [show A10K2.u3091 = KTree.node A10K2.u3087 (nat_lit 49249677) (nat_lit 3095574142) (nat_lit 0) A10K2.u3090 from rfl, allE_node, arows3087, irow3091, arows3090]
  all_goals rfl

theorem atot3091 : totK PA10K2 A10K2.u3091 = [0, 1043199159673, 5595025895892, 11652383158105, 12498174896616, 7095568235969, 1470801809194, 75074572474, 0, 0] := by
  rw [show A10K2.u3091 = KTree.node A10K2.u3087 (nat_lit 49249677) (nat_lit 3095574142) (nat_lit 0) A10K2.u3090 from rfl, totK_node, atot3087, atot3090]
  decide +kernel

theorem arows3098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3098 = true := by
  rw [show A10K2.u3098 = KTree.node A10K2.u3094 (nat_lit 49840966) (nat_lit 10737972368) (nat_lit 0) A10K2.u3097 from rfl, allE_node, arows3094, irow3098, arows3097]
  all_goals rfl

theorem atot3098 : totK PA10K2 A10K2.u3098 = [0, 827520024373, 5637217354605, 13675343953464, 13799254668323, 5125869893552, 598231441794, 12477124820, 0, 0] := by
  rw [show A10K2.u3098 = KTree.node A10K2.u3094 (nat_lit 49840966) (nat_lit 10737972368) (nat_lit 0) A10K2.u3097 from rfl, totK_node, atot3094, atot3097]
  decide +kernel

theorem arows3107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3107 = true := by
  rw [show A10K2.u3107 = KTree.node A10K2.u3103 (nat_lit 49890977) (nat_lit 3850674724) (nat_lit 0) A10K2.u3106 from rfl, allE_node, arows3103, irow3107, arows3106]
  all_goals rfl

theorem atot3107 : totK PA10K2 A10K2.u3107 = [0, 2133734795744, 10122260871857, 16055004859218, 9513542991029, 1878035990346, 95906887612, 0, 0, 0] := by
  rw [show A10K2.u3107 = KTree.node A10K2.u3103 (nat_lit 49890977) (nat_lit 3850674724) (nat_lit 0) A10K2.u3106 from rfl, totK_node, atot3103, atot3106]
  decide +kernel

theorem arows3114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3114 = true := by
  rw [show A10K2.u3114 = KTree.node A10K2.u3110 (nat_lit 49924338) (nat_lit 14113540732) (nat_lit 0) A10K2.u3113 from rfl, allE_node, arows3110, irow3114, arows3113]
  all_goals rfl

theorem atot3114 : totK PA10K2 A10K2.u3114 = [0, 725949308331, 4900375987717, 12655266731873, 14289406038327, 5940550914755, 674866296433, 12696458652, 0, 0] := by
  rw [show A10K2.u3114 = KTree.node A10K2.u3110 (nat_lit 49924338) (nat_lit 14113540732) (nat_lit 0) A10K2.u3113 from rfl, totK_node, atot3110, atot3113]
  decide +kernel

theorem arows3122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3122 = true := by
  rw [show A10K2.u3122 = KTree.node A10K2.u3118 (nat_lit 50028607) (nat_lit 13987994865) (nat_lit 0) A10K2.u3121 from rfl, allE_node, arows3118, irow3122, arows3121]
  all_goals rfl

theorem atot3122 : totK PA10K2 A10K2.u3122 = [0, 1663055897621, 8717359995530, 15727133621694, 10767230089750, 2343918044907, 115793343942, 0, 0, 0] := by
  rw [show A10K2.u3122 = KTree.node A10K2.u3118 (nat_lit 50028607) (nat_lit 13987994865) (nat_lit 0) A10K2.u3121 from rfl, totK_node, atot3118, atot3121]
  decide +kernel

theorem arows3129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3129 = true := by
  rw [show A10K2.u3129 = KTree.node A10K2.u3125 (nat_lit 50050747) (nat_lit 6967369810) (nat_lit 0) A10K2.u3128 from rfl, allE_node, arows3125, irow3129, arows3128]
  all_goals rfl

theorem atot3129 : totK PA10K2 A10K2.u3129 = [0, 0, 2096447096876, 10188017349509, 16265756677716, 9237816466892, 1409576510805, 37751669437, 0, 0] := by
  rw [show A10K2.u3129 = KTree.node A10K2.u3125 (nat_lit 50050747) (nat_lit 6967369810) (nat_lit 0) A10K2.u3128 from rfl, totK_node, atot3125, atot3128]
  decide +kernel

theorem arows3139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3139 = true := by
  rw [show A10K2.u3139 = KTree.node A10K2.u3135 (nat_lit 50094535) (nat_lit 14390858342) (nat_lit 0) A10K2.u3138 from rfl, allE_node, arows3135, irow3139, arows3138]
  all_goals rfl

theorem atot3139 : totK PA10K2 A10K2.u3139 = [0, 0, 1866930874319, 9280914538707, 15755085342453, 10319887081069, 2202479604514, 124635997160, 0, 0] := by
  rw [show A10K2.u3139 = KTree.node A10K2.u3135 (nat_lit 50094535) (nat_lit 14390858342) (nat_lit 0) A10K2.u3138 from rfl, totK_node, atot3135, atot3138]
  decide +kernel

theorem arows3146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3146 = true := by
  rw [show A10K2.u3146 = KTree.node A10K2.u3142 (nat_lit 50145064) (nat_lit 4844394506) (nat_lit 0) A10K2.u3145 from rfl, allE_node, arows3142, irow3146, arows3145]
  all_goals rfl

theorem atot3146 : totK PA10K2 A10K2.u3146 = [0, 0, 1516431583584, 7845669474501, 14645639265038, 11726246234856, 3425614500446, 312169436797, 6725424603, 0] := by
  rw [show A10K2.u3146 = KTree.node A10K2.u3142 (nat_lit 50145064) (nat_lit 4844394506) (nat_lit 0) A10K2.u3145 from rfl, totK_node, atot3142, atot3145]
  decide +kernel

theorem arows3154 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3154 = true := by
  rw [show A10K2.u3154 = KTree.node A10K2.u3150 (nat_lit 50179301) (nat_lit 5544974122) (nat_lit 0) A10K2.u3153 from rfl, allE_node, arows3150, irow3154, arows3153]
  all_goals rfl

theorem atot3154 : totK PA10K2 A10K2.u3154 = [0, 0, 901642122145, 6174298716334, 14375561247649, 13521920543225, 4336748237208, 385682273029, 6860445330, 0] := by
  rw [show A10K2.u3154 = KTree.node A10K2.u3150 (nat_lit 50179301) (nat_lit 5544974122) (nat_lit 0) A10K2.u3153 from rfl, totK_node, atot3150, atot3153]
  decide +kernel

theorem arows3161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3161 = true := by
  rw [show A10K2.u3161 = KTree.node A10K2.u3157 (nat_lit 50280118) (nat_lit 15439386157) (nat_lit 0) A10K2.u3160 from rfl, allE_node, arows3157, irow3161, arows3160]
  all_goals rfl

theorem atot3161 : totK PA10K2 A10K2.u3161 = [0, 0, 2089778156043, 10109690794456, 16262166453693, 9451219544165, 1399167141084, 37266124818, 0, 0] := by
  rw [show A10K2.u3161 = KTree.node A10K2.u3157 (nat_lit 50280118) (nat_lit 15439386157) (nat_lit 0) A10K2.u3160 from rfl, totK_node, atot3157, atot3160]
  decide +kernel

theorem arows3170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3170 = true := by
  rw [show A10K2.u3170 = KTree.node A10K2.u3166 (nat_lit 50310884) (nat_lit 8319450498) (nat_lit 0) A10K2.u3169 from rfl, allE_node, arows3166, irow3170, arows3169]
  all_goals rfl

theorem atot3170 : totK PA10K2 A10K2.u3170 = [0, 0, 0, 2356010161507, 10933768661228, 16397361595190, 8128800191404, 1090806953894, 24890466657, 0] := by
  rw [show A10K2.u3170 = KTree.node A10K2.u3166 (nat_lit 50310884) (nat_lit 8319450498) (nat_lit 0) A10K2.u3169 from rfl, totK_node, atot3166, atot3169]
  decide +kernel

theorem arows3177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3177 = true := by
  rw [show A10K2.u3177 = KTree.node A10K2.u3173 (nat_lit 55132933) (nat_lit 6920038188) (nat_lit 0) A10K2.u3176 from rfl, allE_node, arows3173, irow3177, arows3176]
  all_goals rfl

theorem atot3177 : totK PA10K2 A10K2.u3177 = [0, 2384474177162, 10498227139435, 14975260974949, 7484780334539, 1783295627684, 1198354127725, 511713723036, 48886019071, 0] := by
  rw [show A10K2.u3177 = KTree.node A10K2.u3173 (nat_lit 55132933) (nat_lit 6920038188) (nat_lit 0) A10K2.u3176 from rfl, totK_node, atot3173, atot3176]
  decide +kernel

theorem arows3185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3185 = true := by
  rw [show A10K2.u3185 = KTree.node A10K2.u3181 (nat_lit 55163176) (nat_lit 10267680886) (nat_lit 0) A10K2.u3184 from rfl, allE_node, arows3181, irow3185, arows3184]
  all_goals rfl

theorem atot3185 : totK PA10K2 A10K2.u3185 = [0, 0, 2802361685565, 11900581493826, 15917549342804, 6954320496464, 935539488785, 37204059898, 0, 0] := by
  rw [show A10K2.u3185 = KTree.node A10K2.u3181 (nat_lit 55163176) (nat_lit 10267680886) (nat_lit 0) A10K2.u3184 from rfl, totK_node, atot3181, atot3184]
  decide +kernel

theorem arows3192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3192 = true := by
  rw [show A10K2.u3192 = KTree.node A10K2.u3188 (nat_lit 55194924) (nat_lit 13128878353) (nat_lit 0) A10K2.u3191 from rfl, allE_node, arows3188, irow3192, arows3191]
  all_goals rfl

theorem atot3192 : totK PA10K2 A10K2.u3192 = [0, 2002693624572, 9587057040985, 15285160263639, 9061601673614, 1829483138535, 97254275202, 0, 0, 0] := by
  rw [show A10K2.u3192 = KTree.node A10K2.u3188 (nat_lit 55194924) (nat_lit 13128878353) (nat_lit 0) A10K2.u3191 from rfl, totK_node, atot3188, atot3191]
  decide +kernel

theorem arows3203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3203 = true := by
  rw [show A10K2.u3203 = KTree.node A10K2.u3199 (nat_lit 55234861) (nat_lit 6613758113) (nat_lit 0) A10K2.u3202 from rfl, allE_node, arows3199, irow3203, arows3202]
  all_goals rfl

theorem atot3203 : totK PA10K2 A10K2.u3203 = [0, 1293755989507, 6994135731114, 14218356337409, 12240083699499, 3590435975865, 325178756563, 6354482628, 0, 0] := by
  rw [show A10K2.u3203 = KTree.node A10K2.u3199 (nat_lit 55234861) (nat_lit 6613758113) (nat_lit 0) A10K2.u3202 from rfl, totK_node, atot3199, atot3202]
  decide +kernel

theorem arows3210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3210 = true := by
  rw [show A10K2.u3210 = KTree.node A10K2.u3206 (nat_lit 55277270) (nat_lit 13661861614) (nat_lit 0) A10K2.u3209 from rfl, allE_node, arows3206, irow3210, arows3209]
  all_goals rfl

theorem atot3210 : totK PA10K2 A10K2.u3210 = [0, 836871677580, 6119600587871, 14701320347613, 13719865683564, 4364072111886, 318596110187, 0, 0, 0] := by
  rw [show A10K2.u3210 = KTree.node A10K2.u3206 (nat_lit 55277270) (nat_lit 13661861614) (nat_lit 0) A10K2.u3209 from rfl, totK_node, atot3206, atot3209]
  decide +kernel

theorem arows3218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3218 = true := by
  rw [show A10K2.u3218 = KTree.node A10K2.u3214 (nat_lit 55311809) (nat_lit 9494153503) (nat_lit 0) A10K2.u3217 from rfl, allE_node, arows3214, irow3218, arows3217]
  all_goals rfl

theorem atot3218 : totK PA10K2 A10K2.u3218 = [0, 0, 1971043914729, 9533796907942, 15740237740243, 9890407712429, 1913513789996, 86327318925, 0, 0] := by
  rw [show A10K2.u3218 = KTree.node A10K2.u3214 (nat_lit 55311809) (nat_lit 9494153503) (nat_lit 0) A10K2.u3217 from rfl, totK_node, atot3214, atot3217]
  decide +kernel

theorem arows3225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3225 = true := by
  rw [show A10K2.u3225 = KTree.node A10K2.u3221 (nat_lit 55407830) (nat_lit 15000960781) (nat_lit 0) A10K2.u3224 from rfl, allE_node, arows3221, irow3225, arows3224]
  all_goals rfl

theorem atot3225 : totK PA10K2 A10K2.u3225 = [0, 0, 1245509902467, 7112100306441, 14155409174674, 11543188643045, 4009936954137, 611924525855, 31018567651, 0] := by
  rw [show A10K2.u3225 = KTree.node A10K2.u3221 (nat_lit 55407830) (nat_lit 15000960781) (nat_lit 0) A10K2.u3224 from rfl, totK_node, atot3221, atot3224]
  decide +kernel

theorem arows3234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3234 = true := by
  rw [show A10K2.u3234 = KTree.node A10K2.u3230 (nat_lit 55443797) (nat_lit 6723517907) (nat_lit 0) A10K2.u3233 from rfl, allE_node, arows3230, irow3234, arows3233]
  all_goals rfl

theorem atot3234 : totK PA10K2 A10K2.u3234 = [0, 0, 1228183877304, 6966760405373, 14111032953599, 11742353143961, 3530327376749, 337596541637, 5685526223, 0] := by
  rw [show A10K2.u3234 = KTree.node A10K2.u3230 (nat_lit 55443797) (nat_lit 6723517907) (nat_lit 0) A10K2.u3233 from rfl, totK_node, atot3230, atot3233]
  decide +kernel

theorem arows3241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3241 = true := by
  rw [show A10K2.u3241 = KTree.node A10K2.u3237 (nat_lit 55485805) (nat_lit 6246467135) (nat_lit 0) A10K2.u3240 from rfl, allE_node, arows3237, irow3241, arows3240]
  all_goals rfl

theorem atot3241 : totK PA10K2 A10K2.u3241 = [0, 0, 961894000082, 6248206663847, 14032301600499, 12201493567107, 3339637730240, 308729779796, 6239673734, 0] := by
  rw [show A10K2.u3241 = KTree.node A10K2.u3237 (nat_lit 55485805) (nat_lit 6246467135) (nat_lit 0) A10K2.u3240 from rfl, totK_node, atot3237, atot3240]
  decide +kernel

theorem arows3249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3249 = true := by
  rw [show A10K2.u3249 = KTree.node A10K2.u3245 (nat_lit 55524361) (nat_lit 7610048824) (nat_lit 0) A10K2.u3248 from rfl, allE_node, arows3245, irow3249, arows3248]
  all_goals rfl

theorem atot3249 : totK PA10K2 A10K2.u3249 = [0, 292640272425, 2757141959690, 10004166418667, 15621409866519, 9504921693737, 1807424467873, 79757387231, 0, 0] := by
  rw [show A10K2.u3249 = KTree.node A10K2.u3245 (nat_lit 55524361) (nat_lit 7610048824) (nat_lit 0) A10K2.u3248 from rfl, totK_node, atot3245, atot3248]
  decide +kernel

theorem arows3256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3256 = true := by
  rw [show A10K2.u3256 = KTree.node A10K2.u3252 (nat_lit 55597853) (nat_lit 6284307410) (nat_lit 0) A10K2.u3255 from rfl, allE_node, arows3252, irow3256, arows3255]
  all_goals rfl

theorem atot3256 : totK PA10K2 A10K2.u3256 = [0, 1324005672777, 7512682500237, 14679680367640, 11111469380995, 2950580789346, 266955376096, 5546304973, 0, 0] := by
  rw [show A10K2.u3256 = KTree.node A10K2.u3252 (nat_lit 55597853) (nat_lit 6284307410) (nat_lit 0) A10K2.u3255 from rfl, totK_node, atot3252, atot3255]
  decide +kernel

theorem arows3266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3266 = true := by
  rw [show A10K2.u3266 = KTree.node A10K2.u3262 (nat_lit 55659056) (nat_lit 10308967583) (nat_lit 0) A10K2.u3265 from rfl, allE_node, arows3262, irow3266, arows3265]
  all_goals rfl

theorem atot3266 : totK PA10K2 A10K2.u3266 = [0, 1879963097768, 9513023272292, 15988339629930, 9706230906444, 1858086133266, 86472468908, 0, 0, 0] := by
  rw [show A10K2.u3266 = KTree.node A10K2.u3262 (nat_lit 55659056) (nat_lit 10308967583) (nat_lit 0) A10K2.u3265 from rfl, totK_node, atot3262, atot3265]
  decide +kernel

theorem arows3273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3273 = true := by
  rw [show A10K2.u3273 = KTree.node A10K2.u3269 (nat_lit 55691824) (nat_lit 10308967583) (nat_lit 0) A10K2.u3272 from rfl, allE_node, arows3269, irow3273, arows3272]
  all_goals rfl

theorem atot3273 : totK PA10K2 A10K2.u3273 = [0, 582799510374, 4225137447589, 11613986851657, 14141716342887, 6580778430388, 944200639747, 37204059898, 0, 0] := by
  rw [show A10K2.u3273 = KTree.node A10K2.u3269 (nat_lit 55691824) (nat_lit 10308967583) (nat_lit 0) A10K2.u3272 from rfl, totK_node, atot3269, atot3272]
  decide +kernel

theorem arows3281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3281 = true := by
  rw [show A10K2.u3281 = KTree.node A10K2.u3277 (nat_lit 55722784) (nat_lit 13255786215) (nat_lit 0) A10K2.u3280 from rfl, allE_node, arows3277, irow3281, arows3280]
  all_goals rfl

theorem atot3281 : totK PA10K2 A10K2.u3281 = [0, 1591323679956, 8598285708494, 15485587070111, 10106977045804, 1993841827485, 101461561920, 0, 0, 0] := by
  rw [show A10K2.u3281 = KTree.node A10K2.u3277 (nat_lit 55722784) (nat_lit 13255786215) (nat_lit 0) A10K2.u3280 from rfl, totK_node, atot3277, atot3280]
  decide +kernel

theorem arows3288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3288 = true := by
  rw [show A10K2.u3288 = KTree.node A10K2.u3284 (nat_lit 55837105) (nat_lit 9602706401) (nat_lit 0) A10K2.u3287 from rfl, allE_node, arows3284, irow3288, arows3287]
  all_goals rfl

theorem atot3288 : totK PA10K2 A10K2.u3288 = [0, 0, 2583597137470, 11607651495856, 16079371718391, 6579535823808, 747500422486, 11801668502, 0, 0] := by
  rw [show A10K2.u3288 = KTree.node A10K2.u3284 (nat_lit 55837105) (nat_lit 9602706401) (nat_lit 0) A10K2.u3287 from rfl, totK_node, atot3284, atot3287]
  decide +kernel

theorem arows3297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3297 = true := by
  rw [show A10K2.u3297 = KTree.node A10K2.u3293 (nat_lit 55920301) (nat_lit 5985846871) (nat_lit 0) A10K2.u3296 from rfl, allE_node, arows3293, irow3297, arows3296]
  all_goals rfl

theorem atot3297 : totK PA10K2 A10K2.u3297 = [0, 0, 2301397980885, 10471483712179, 15913291349070, 8651692941516, 1359502304936, 51124281457, 0, 0] := by
  rw [show A10K2.u3297 = KTree.node A10K2.u3293 (nat_lit 55920301) (nat_lit 5985846871) (nat_lit 0) A10K2.u3296 from rfl, totK_node, atot3293, atot3296]
  decide +kernel

theorem arows3304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3304 = true := by
  rw [show A10K2.u3304 = KTree.node A10K2.u3300 (nat_lit 55982116) (nat_lit 13706456614) (nat_lit 0) A10K2.u3303 from rfl, allE_node, arows3300, irow3304, arows3303]
  all_goals rfl

theorem atot3304 : totK PA10K2 A10K2.u3304 = [0, 0, 2066925538606, 10111430324752, 15926922655312, 8105075624615, 1215483127151, 48204412704, 0, 0] := by
  rw [show A10K2.u3304 = KTree.node A10K2.u3300 (nat_lit 55982116) (nat_lit 13706456614) (nat_lit 0) A10K2.u3303 from rfl, totK_node, atot3300, atot3303]
  decide +kernel

theorem arows3312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3312 = true := by
  rw [show A10K2.u3312 = KTree.node A10K2.u3308 (nat_lit 56023208) (nat_lit 8735255972) (nat_lit 0) A10K2.u3311 from rfl, allE_node, arows3308, irow3312, arows3311]
  all_goals rfl

theorem atot3312 : totK PA10K2 A10K2.u3312 = [0, 1386233821196, 5686188786486, 9382382079468, 10613540452909, 8569030528391, 2698579458730, 287650416194, 6354482628, 0] := by
  rw [show A10K2.u3312 = KTree.node A10K2.u3308 (nat_lit 56023208) (nat_lit 8735255972) (nat_lit 0) A10K2.u3311 from rfl, totK_node, atot3308, atot3311]
  decide +kernel

theorem arows3319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3319 = true := by
  rw [show A10K2.u3319 = KTree.node A10K2.u3315 (nat_lit 56157368) (nat_lit 10241397227) (nat_lit 0) A10K2.u3318 from rfl, allE_node, arows3315, irow3319, arows3318]
  all_goals rfl

theorem atot3319 : totK PA10K2 A10K2.u3319 = [0, 846901670217, 6013477638595, 14389055991471, 13805758029414, 4609500374612, 461079196136, 7903172220, 0, 0] := by
  rw [show A10K2.u3319 = KTree.node A10K2.u3315 (nat_lit 56157368) (nat_lit 10241397227) (nat_lit 0) A10K2.u3318 from rfl, totK_node, atot3315, atot3318]
  decide +kernel

theorem arows3331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3331 = true := by
  rw [show A10K2.u3331 = KTree.node A10K2.u3327 (nat_lit 56193592) (nat_lit 14641701130) (nat_lit 0) A10K2.u3330 from rfl, allE_node, arows3327, irow3331, arows3330]
  all_goals rfl

theorem atot3331 : totK PA10K2 A10K2.u3331 = [0, 1371842486777, 7357429804513, 14215139783475, 11775706796028, 4056155647330, 540201065700, 25565504801, 0, 0] := by
  rw [show A10K2.u3331 = KTree.node A10K2.u3327 (nat_lit 56193592) (nat_lit 14641701130) (nat_lit 0) A10K2.u3330 from rfl, totK_node, atot3327, atot3330]
  decide +kernel

theorem arows3338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3338 = true := by
  rw [show A10K2.u3338 = KTree.node A10K2.u3334 (nat_lit 56295497) (nat_lit 9594707706) (nat_lit 0) A10K2.u3337 from rfl, allE_node, arows3334, irow3338, arows3337]
  all_goals rfl

theorem atot3338 : totK PA10K2 A10K2.u3338 = [0, 1410911442132, 7485018370084, 14364124365391, 11879512079238, 3986226826469, 453896971689, 11638555097, 0, 0] := by
  rw [show A10K2.u3338 = KTree.node A10K2.u3334 (nat_lit 56295497) (nat_lit 9594707706) (nat_lit 0) A10K2.u3337 from rfl, totK_node, atot3334, atot3337]
  decide +kernel

theorem arows3346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3346 = true := by
  rw [show A10K2.u3346 = KTree.node A10K2.u3342 (nat_lit 56327408) (nat_lit 11224612186) (nat_lit 0) A10K2.u3345 from rfl, allE_node, arows3342, irow3346, arows3345]
  all_goals rfl

theorem atot3346 : totK PA10K2 A10K2.u3346 = [0, 873803232168, 5972342389444, 14248922373054, 13673742086235, 4592181761812, 427707805102, 6904928264, 0, 0] := by
  rw [show A10K2.u3346 = KTree.node A10K2.u3342 (nat_lit 56327408) (nat_lit 11224612186) (nat_lit 0) A10K2.u3345 from rfl, totK_node, atot3342, atot3345]
  decide +kernel

theorem arows3353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3353 = true := by
  rw [show A10K2.u3353 = KTree.node A10K2.u3349 (nat_lit 56359969) (nat_lit 8667826070) (nat_lit 0) A10K2.u3352 from rfl, allE_node, arows3349, irow3353, arows3352]
  all_goals rfl

theorem atot3353 : totK PA10K2 A10K2.u3353 = [0, 0, 2256745169612, 10476908292817, 16280283380950, 9338625733702, 1677963362306, 76060323778, 0, 0] := by
  rw [show A10K2.u3353 = KTree.node A10K2.u3349 (nat_lit 56359969) (nat_lit 8667826070) (nat_lit 0) A10K2.u3352 from rfl, totK_node, atot3349, atot3352]
  decide +kernel

theorem arows3362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3362 = true := by
  rw [show A10K2.u3362 = KTree.node A10K2.u3358 (nat_lit 56422326) (nat_lit 17080749001) (nat_lit 0) A10K2.u3361 from rfl, allE_node, arows3358, irow3362, arows3361]
  all_goals rfl

theorem atot3362 : totK PA10K2 A10K2.u3362 = [0, 0, 1323561668771, 7798826274080, 15754141548265, 12171067564129, 2885462739362, 166060223335, 0, 0] := by
  rw [show A10K2.u3362 = KTree.node A10K2.u3358 (nat_lit 56422326) (nat_lit 17080749001) (nat_lit 0) A10K2.u3361 from rfl, totK_node, atot3358, atot3361]
  decide +kernel

theorem arows3369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3369 = true := by
  rw [show A10K2.u3369 = KTree.node A10K2.u3365 (nat_lit 56458757) (nat_lit 2899547384) (nat_lit 0) A10K2.u3368 from rfl, allE_node, arows3365, irow3369, arows3368]
  all_goals rfl

theorem atot3369 : totK PA10K2 A10K2.u3369 = [0, 0, 895182488223, 6480672344383, 14716610646407, 12805321460260, 4028061593100, 396611943509, 7151180950, 0] := by
  rw [show A10K2.u3369 = KTree.node A10K2.u3365 (nat_lit 56458757) (nat_lit 2899547384) (nat_lit 0) A10K2.u3368 from rfl, totK_node, atot3365, atot3368]
  decide +kernel

theorem arows3377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3377 = true := by
  rw [show A10K2.u3377 = KTree.node A10K2.u3373 (nat_lit 56567515) (nat_lit 9729745405) (nat_lit 0) A10K2.u3376 from rfl, allE_node, arows3373, irow3377, arows3376]
  all_goals rfl

theorem atot3377 : totK PA10K2 A10K2.u3377 = [0, 0, 2283220196760, 10285602391200, 15948181453931, 9690750481492, 1875738571304, 74753130362, 0, 0] := by
  rw [show A10K2.u3377 = KTree.node A10K2.u3373 (nat_lit 56567515) (nat_lit 9729745405) (nat_lit 0) A10K2.u3376 from rfl, totK_node, atot3373, atot3376]
  decide +kernel

theorem arows3384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3384 = true := by
  rw [show A10K2.u3384 = KTree.node A10K2.u3380 (nat_lit 56600388) (nat_lit 5174987568) (nat_lit 0) A10K2.u3383 from rfl, allE_node, arows3380, irow3384, arows3383]
  all_goals rfl

theorem atot3384 : totK PA10K2 A10K2.u3384 = [0, 0, 0, 3261489817417, 13261064962063, 16431420434450, 6472789012772, 590841624572, 6439430839, 0] := by
  rw [show A10K2.u3384 = KTree.node A10K2.u3380 (nat_lit 56600388) (nat_lit 5174987568) (nat_lit 0) A10K2.u3383 from rfl, totK_node, atot3380, atot3383]
  decide +kernel

theorem arows3394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3394 = true := by
  rw [show A10K2.u3394 = KTree.node A10K2.u3390 (nat_lit 57228062) (nat_lit 7898756820) (nat_lit 0) A10K2.u3393 from rfl, allE_node, arows3390, irow3394, arows3393]
  all_goals rfl

theorem atot3394 : totK PA10K2 A10K2.u3394 = [0, 0, 2326504769392, 9696375689505, 13946741247099, 8589184712432, 3210767104569, 721178113847, 41875219570, 0] := by
  rw [show A10K2.u3394 = KTree.node A10K2.u3390 (nat_lit 57228062) (nat_lit 7898756820) (nat_lit 0) A10K2.u3393 from rfl, totK_node, atot3390, atot3393]
  decide +kernel

theorem arows3401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3401 = true := by
  rw [show A10K2.u3401 = KTree.node A10K2.u3397 (nat_lit 57259512) (nat_lit 5565562067) (nat_lit 0) A10K2.u3400 from rfl, allE_node, arows3397, irow3401, arows3400]
  all_goals rfl

theorem atot3401 : totK PA10K2 A10K2.u3401 = [0, 0, 45770322325, 3361476890300, 12482326516105, 15177666387957, 6381291704202, 903210454356, 37204059898, 0] := by
  rw [show A10K2.u3401 = KTree.node A10K2.u3397 (nat_lit 57259512) (nat_lit 5565562067) (nat_lit 0) A10K2.u3400 from rfl, totK_node, atot3397, atot3400]
  decide +kernel

theorem arows3409 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3409 = true := by
  rw [show A10K2.u3409 = KTree.node A10K2.u3405 (nat_lit 57290708) (nat_lit 6303659676) (nat_lit 0) A10K2.u3408 from rfl, allE_node, arows3405, irow3409, arows3408]
  all_goals rfl

theorem atot3409 : totK PA10K2 A10K2.u3409 = [0, 0, 1998650869895, 9557743088236, 15354721059086, 9073805089476, 1814054943853, 104859417043, 0, 0] := by
  rw [show A10K2.u3409 = KTree.node A10K2.u3405 (nat_lit 57290708) (nat_lit 6303659676) (nat_lit 0) A10K2.u3408 from rfl, totK_node, atot3405, atot3408]
  decide +kernel

theorem arows3416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3416 = true := by
  rw [show A10K2.u3416 = KTree.node A10K2.u3412 (nat_lit 57331756) (nat_lit 12012785051) (nat_lit 0) A10K2.u3415 from rfl, allE_node, arows3412, irow3416, arows3415]
  all_goals rfl

theorem atot3416 : totK PA10K2 A10K2.u3416 = [0, 0, 1290752091112, 7124727727256, 14375573524081, 12045892227697, 3307948805249, 302990348673, 6354482628, 0] := by
  rw [show A10K2.u3416 = KTree.node A10K2.u3412 (nat_lit 57331756) (nat_lit 12012785051) (nat_lit 0) A10K2.u3415 from rfl, totK_node, atot3412, atot3415]
  decide +kernel

theorem arows3425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3425 = true := by
  rw [show A10K2.u3425 = KTree.node A10K2.u3421 (nat_lit 57376240) (nat_lit 13804357183) (nat_lit 0) A10K2.u3424 from rfl, allE_node, arows3421, irow3425, arows3424]
  all_goals rfl

theorem atot3425 : totK PA10K2 A10K2.u3425 = [0, 0, 834905328705, 5980508658907, 14434430026528, 13668259935721, 4694121740400, 455853968871, 7047025452, 0] := by
  rw [show A10K2.u3425 = KTree.node A10K2.u3421 (nat_lit 57376240) (nat_lit 13804357183) (nat_lit 0) A10K2.u3424 from rfl, totK_node, atot3421, atot3424]
  decide +kernel

theorem arows3432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3432 = true := by
  rw [show A10K2.u3432 = KTree.node A10K2.u3428 (nat_lit 57486911) (nat_lit 14091572107) (nat_lit 0) A10K2.u3431 from rfl, allE_node, arows3428, irow3432, arows3431]
  all_goals rfl

theorem atot3432 : totK PA10K2 A10K2.u3432 = [0, 0, 0, 2197630777840, 10451989788280, 15966616680614, 8420452053250, 1383365374883, 67517432236, 0] := by
  rw [show A10K2.u3432 = KTree.node A10K2.u3428 (nat_lit 57486911) (nat_lit 14091572107) (nat_lit 0) A10K2.u3431 from rfl, totK_node, atot3428, atot3431]
  decide +kernel

theorem arows3440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3440 = true := by
  rw [show A10K2.u3440 = KTree.node A10K2.u3436 (nat_lit 57519252) (nat_lit 10750349994) (nat_lit 0) A10K2.u3439 from rfl, allE_node, arows3436, irow3440, arows3439]
  all_goals rfl

theorem atot3440 : totK PA10K2 A10K2.u3440 = [0, 0, 0, 777446694424, 5066772054476, 12713043521954, 13455055989362, 5314190608507, 730524786404, 31018567651] := by
  rw [show A10K2.u3440 = KTree.node A10K2.u3436 (nat_lit 57519252) (nat_lit 10750349994) (nat_lit 0) A10K2.u3439 from rfl, totK_node, atot3436, atot3439]
  decide +kernel

theorem arows3447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3447 = true := by
  rw [show A10K2.u3447 = KTree.node A10K2.u3443 (nat_lit 57552023) (nat_lit 13890710332) (nat_lit 0) A10K2.u3446 from rfl, allE_node, arows3443, irow3447, arows3446]
  all_goals rfl

theorem atot3447 : totK PA10K2 A10K2.u3447 = [0, 0, 0, 1994586508952, 9808105990435, 15311525594938, 8470409534327, 1860974595129, 203051212470, 5685526223] := by
  rw [show A10K2.u3447 = KTree.node A10K2.u3443 (nat_lit 57552023) (nat_lit 13890710332) (nat_lit 0) A10K2.u3446 from rfl, totK_node, atot3443, atot3446]
  decide +kernel

theorem arows3458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3458 = true := by
  rw [show A10K2.u3458 = KTree.node A10K2.u3454 (nat_lit 57593857) (nat_lit 10581725467) (nat_lit 0) A10K2.u3457 from rfl, allE_node, arows3454, irow3458, arows3457]
  all_goals rfl

theorem atot3458 : totK PA10K2 A10K2.u3458 = [0, 0, 0, 1287648500790, 7161950318798, 14562630275492, 11733353772675, 3127627047778, 297264644523, 5982052406] := by
  rw [show A10K2.u3458 = KTree.node A10K2.u3454 (nat_lit 57593857) (nat_lit 10581725467) (nat_lit 0) A10K2.u3457 from rfl, totK_node, atot3454, atot3457]
  decide +kernel

theorem arows3465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3465 = true := by
  rw [show A10K2.u3465 = KTree.node A10K2.u3461 (nat_lit 57674401) (nat_lit 7888112313) (nat_lit 0) A10K2.u3464 from rfl, allE_node, arows3461, irow3465, arows3464]
  all_goals rfl

theorem atot3465 : totK PA10K2 A10K2.u3465 = [0, 0, 1297955991958, 7231236764338, 14066900650802, 11327483825398, 4231662358274, 695675010383, 36702257158, 0] := by
  rw [show A10K2.u3465 = KTree.node A10K2.u3461 (nat_lit 57674401) (nat_lit 7888112313) (nat_lit 0) A10K2.u3464 from rfl, totK_node, atot3461, atot3464]
  decide +kernel

theorem arows3473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3473 = true := by
  rw [show A10K2.u3473 = KTree.node A10K2.u3469 (nat_lit 57748877) (nat_lit 11933677) (nat_lit 0) A10K2.u3472 from rfl, allE_node, arows3469, irow3473, arows3472]
  all_goals rfl

theorem atot3473 : totK PA10K2 A10K2.u3473 = [0, 0, 1600074267320, 8217664529189, 14805890329652, 10577830074730, 2530345415197, 192542041105, 5546304973, 0] := by
  rw [show A10K2.u3473 = KTree.node A10K2.u3469 (nat_lit 57748877) (nat_lit 11933677) (nat_lit 0) A10K2.u3472 from rfl, totK_node, atot3469, atot3472]
  decide +kernel

theorem arows3480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3480 = true := by
  rw [show A10K2.u3480 = KTree.node A10K2.u3476 (nat_lit 57781717) (nat_lit 4508823180) (nat_lit 0) A10K2.u3479 from rfl, allE_node, arows3476, irow3480, arows3479]
  all_goals rfl

theorem atot3480 : totK PA10K2 A10K2.u3480 = [0, 0, 588004983511, 4421076561003, 12467533450555, 14414378136607, 5837894790436, 769572755434, 31082886609, 0] := by
  rw [show A10K2.u3480 = KTree.node A10K2.u3476 (nat_lit 57781717) (nat_lit 4508823180) (nat_lit 0) A10K2.u3479 from rfl, totK_node, atot3476, atot3479]
  decide +kernel

theorem arows3489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3489 = true := by
  rw [show A10K2.u3489 = KTree.node A10K2.u3485 (nat_lit 57812833) (nat_lit 5065238055) (nat_lit 0) A10K2.u3488 from rfl, allE_node, arows3485, irow3489, arows3488]
  all_goals rfl

theorem atot3489 : totK PA10K2 A10K2.u3489 = [0, 0, 2171906535597, 9824544232512, 15049074757660, 8834286231268, 2093360986561, 223203206639, 6121173289, 0] := by
  rw [show A10K2.u3489 = KTree.node A10K2.u3485 (nat_lit 57812833) (nat_lit 5065238055) (nat_lit 0) A10K2.u3488 from rfl, totK_node, atot3485, atot3488]
  decide +kernel

theorem arows3496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3496 = true := by
  rw [show A10K2.u3496 = KTree.node A10K2.u3492 (nat_lit 57852360) (nat_lit 12962404075) (nat_lit 0) A10K2.u3495 from rfl, allE_node, arows3492, irow3496, arows3495]
  all_goals rfl

theorem atot3496 : totK PA10K2 A10K2.u3496 = [0, 0, 0, 3856279865981, 14097713829920, 14893535672585, 4205368933799, 351050720477, 6354482628, 0] := by
  rw [show A10K2.u3496 = KTree.node A10K2.u3492 (nat_lit 57852360) (nat_lit 12962404075) (nat_lit 0) A10K2.u3495 from rfl, totK_node, atot3492, atot3495]
  decide +kernel

theorem arows3504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3504 = true := by
  rw [show A10K2.u3504 = KTree.node A10K2.u3500 (nat_lit 58013375) (nat_lit 9560490173) (nat_lit 0) A10K2.u3503 from rfl, allE_node, arows3500, irow3504, arows3503]
  all_goals rfl

theorem atot3504 : totK PA10K2 A10K2.u3504 = [0, 0, 0, 2315865535699, 10755956975184, 15995744218197, 7721619585758, 1095033309551, 44161539106, 0] := by
  rw [show A10K2.u3504 = KTree.node A10K2.u3500 (nat_lit 58013375) (nat_lit 9560490173) (nat_lit 0) A10K2.u3503 from rfl, totK_node, atot3500, atot3503]
  decide +kernel

theorem arows3511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3511 = true := by
  rw [show A10K2.u3511 = KTree.node A10K2.u3507 (nat_lit 58075299) (nat_lit 10499862237) (nat_lit 0) A10K2.u3510 from rfl, allE_node, arows3507, irow3511, arows3510]
  all_goals rfl

theorem atot3511 : totK PA10K2 A10K2.u3511 = [0, 0, 0, 2460694024440, 11165861424565, 16035215831107, 7335892305266, 1019023932996, 43426679930, 0] := by
  rw [show A10K2.u3511 = KTree.node A10K2.u3507 (nat_lit 58075299) (nat_lit 10499862237) (nat_lit 0) A10K2.u3510 from rfl, totK_node, atot3507, atot3510]
  decide +kernel

theorem arows3521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3521 = true := by
  rw [show A10K2.u3521 = KTree.node A10K2.u3517 (nat_lit 58116264) (nat_lit 8917934252) (nat_lit 0) A10K2.u3520 from rfl, allE_node, arows3517, irow3521, arows3520]
  all_goals rfl

theorem atot3521 : totK PA10K2 A10K2.u3521 = [0, 0, 1385427948510, 5091164601114, 8226052270811, 11187112473948, 9433237319860, 2744333521097, 271960934478, 6354482628] := by
  rw [show A10K2.u3521 = KTree.node A10K2.u3517 (nat_lit 58116264) (nat_lit 8917934252) (nat_lit 0) A10K2.u3520 from rfl, totK_node, atot3517, atot3520]
  decide +kernel

theorem arows3528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3528 = true := by
  rw [show A10K2.u3528 = KTree.node A10K2.u3524 (nat_lit 58276082) (nat_lit 14861961741) (nat_lit 0) A10K2.u3527 from rfl, allE_node, arows3524, irow3528, arows3527]
  all_goals rfl

theorem atot3528 : totK PA10K2 A10K2.u3528 = [0, 0, 2215014219477, 10166829351158, 15796970221168, 9313968160432, 1875093700880, 100459322603, 0, 0] := by
  rw [show A10K2.u3528 = KTree.node A10K2.u3524 (nat_lit 58276082) (nat_lit 14861961741) (nat_lit 0) A10K2.u3527 from rfl, totK_node, atot3524, atot3527]
  decide +kernel

theorem arows3536 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3536 = true := by
  rw [show A10K2.u3536 = KTree.node A10K2.u3532 (nat_lit 58308538) (nat_lit 13748579757) (nat_lit 0) A10K2.u3535 from rfl, allE_node, arows3532, irow3536, arows3535]
  all_goals rfl

theorem atot3536 : totK PA10K2 A10K2.u3536 = [0, 0, 424471676933, 4494175699466, 13378568825507, 14737114447024, 5712596135117, 746631057364, 31082886609, 0] := by
  rw [show A10K2.u3536 = KTree.node A10K2.u3532 (nat_lit 58308538) (nat_lit 13748579757) (nat_lit 0) A10K2.u3535 from rfl, totK_node, atot3532, atot3535]
  decide +kernel

theorem arows3543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3543 = true := by
  rw [show A10K2.u3543 = KTree.node A10K2.u3539 (nat_lit 58408127) (nat_lit 14099527719) (nat_lit 0) A10K2.u3542 from rfl, allE_node, arows3539, irow3543, arows3542]
  all_goals rfl

theorem atot3543 : totK PA10K2 A10K2.u3543 = [0, 0, 1859296062540, 9671285067273, 16485382428977, 10155502775708, 1933844941796, 96554317252, 0, 0] := by
  rw [show A10K2.u3543 = KTree.node A10K2.u3539 (nat_lit 58408127) (nat_lit 14099527719) (nat_lit 0) A10K2.u3542 from rfl, totK_node, atot3539, atot3542]
  decide +kernel

theorem arows3552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3552 = true := by
  rw [show A10K2.u3552 = KTree.node A10K2.u3548 (nat_lit 58451730) (nat_lit 14946702596) (nat_lit 0) A10K2.u3551 from rfl, allE_node, arows3548, irow3552, arows3551]
  all_goals rfl

theorem atot3552 : totK PA10K2 A10K2.u3552 = [0, 840727299041, 3245615607153, 5574847454889, 9782100283758, 12582897152451, 6619579806179, 1110782404136, 48968269916, 0] := by
  rw [show A10K2.u3552 = KTree.node A10K2.u3548 (nat_lit 58451730) (nat_lit 14946702596) (nat_lit 0) A10K2.u3551 from rfl, totK_node, atot3548, atot3551]
  decide +kernel

theorem arows3559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3559 = true := by
  rw [show A10K2.u3559 = KTree.node A10K2.u3555 (nat_lit 58745217) (nat_lit 10320576489) (nat_lit 0) A10K2.u3558 from rfl, allE_node, arows3555, irow3559, arows3558]
  all_goals rfl

theorem atot3559 : totK PA10K2 A10K2.u3559 = [0, 1339580755464, 7709030818767, 15345254631664, 11514809457234, 2740248539519, 159938532092, 0, 0, 0] := by
  rw [show A10K2.u3559 = KTree.node A10K2.u3555 (nat_lit 58745217) (nat_lit 10320576489) (nat_lit 0) A10K2.u3558 from rfl, totK_node, atot3555, atot3558]
  decide +kernel

theorem arows3567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3567 = true := by
  rw [show A10K2.u3567 = KTree.node A10K2.u3563 (nat_lit 58778377) (nat_lit 9706556979) (nat_lit 0) A10K2.u3566 from rfl, allE_node, arows3563, irow3567, arows3566]
  all_goals rfl

theorem atot3567 : totK PA10K2 A10K2.u3567 = [0, 1046080136887, 5831233638915, 12630705521955, 12746409039970, 5301762440824, 807261961698, 36196801203, 0, 0] := by
  rw [show A10K2.u3567 = KTree.node A10K2.u3563 (nat_lit 58778377) (nat_lit 9706556979) (nat_lit 0) A10K2.u3566 from rfl, totK_node, atot3563, atot3566]
  decide +kernel

theorem arows3574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3574 = true := by
  rw [show A10K2.u3574 = KTree.node A10K2.u3570 (nat_lit 58873929) (nat_lit 8505478958) (nat_lit 0) A10K2.u3573 from rfl, allE_node, arows3570, irow3574, arows3573]
  all_goals rfl

theorem atot3574 : totK PA10K2 A10K2.u3574 = [0, 1101614959195, 7284869528334, 15392700688437, 11645997904560, 2560978056394, 148328891790, 0, 0, 0] := by
  rw [show A10K2.u3574 = KTree.node A10K2.u3570 (nat_lit 58873929) (nat_lit 8505478958) (nat_lit 0) A10K2.u3573 from rfl, totK_node, atot3570, atot3573]
  decide +kernel

theorem arows3587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3587 = true := by
  rw [show A10K2.u3587 = KTree.node A10K2.u3583 (nat_lit 58987348) (nat_lit 10622127057) (nat_lit 0) A10K2.u3586 from rfl, allE_node, arows3583, irow3587, arows3586]
  all_goals rfl

theorem atot3587 : totK PA10K2 A10K2.u3587 = [0, 0, 2288309053292, 10686895384376, 15954699026466, 7711525057580, 1138143189576, 42891176429, 0, 0] := by
  rw [show A10K2.u3587 = KTree.node A10K2.u3583 (nat_lit 58987348) (nat_lit 10622127057) (nat_lit 0) A10K2.u3586 from rfl, totK_node, atot3583, atot3586]
  decide +kernel

theorem arows3594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3594 = true := by
  rw [show A10K2.u3594 = KTree.node A10K2.u3590 (nat_lit 59120713) (nat_lit 9510040382) (nat_lit 0) A10K2.u3593 from rfl, allE_node, arows3590, irow3594, arows3593]
  all_goals rfl

theorem atot3594 : totK PA10K2 A10K2.u3594 = [0, 0, 2336438190561, 10900319953337, 16247402772083, 7971653500553, 1130473630630, 43719237455, 0, 0] := by
  rw [show A10K2.u3594 = KTree.node A10K2.u3590 (nat_lit 59120713) (nat_lit 9510040382) (nat_lit 0) A10K2.u3593 from rfl, totK_node, atot3590, atot3593]
  decide +kernel

theorem arows3602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3602 = true := by
  rw [show A10K2.u3602 = KTree.node A10K2.u3598 (nat_lit 59164836) (nat_lit 13773832359) (nat_lit 0) A10K2.u3601 from rfl, allE_node, arows3598, irow3602, arows3601]
  all_goals rfl

theorem atot3602 : totK PA10K2 A10K2.u3602 = [0, 860205094993, 3736700297015, 7840045097040, 12138554283150, 10065278843650, 2823390872467, 267277905582, 5676195732, 0] := by
  rw [show A10K2.u3602 = KTree.node A10K2.u3598 (nat_lit 59164836) (nat_lit 13773832359) (nat_lit 0) A10K2.u3601 from rfl, totK_node, atot3598, atot3601]
  decide +kernel

theorem arows3609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3609 = true := by
  rw [show A10K2.u3609 = KTree.node A10K2.u3605 (nat_lit 59337946) (nat_lit 13957107525) (nat_lit 0) A10K2.u3608 from rfl, allE_node, arows3605, irow3609, arows3608]
  all_goals rfl

theorem atot3609 : totK PA10K2 A10K2.u3609 = [0, 1438061005852, 7827257846050, 14984534928973, 11518343294704, 3205487431543, 341980953968, 20331139758, 0, 0] := by
  rw [show A10K2.u3609 = KTree.node A10K2.u3605 (nat_lit 59337946) (nat_lit 13957107525) (nat_lit 0) A10K2.u3608 from rfl, totK_node, atot3605, atot3608]
  decide +kernel

theorem arows3618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3618 = true := by
  rw [show A10K2.u3618 = KTree.node A10K2.u3614 (nat_lit 59369235) (nat_lit 10787925433) (nat_lit 0) A10K2.u3617 from rfl, allE_node, arows3614, irow3618, arows3617]
  all_goals rfl

theorem atot3618 : totK PA10K2 A10K2.u3618 = [0, 1157305605063, 6038541872452, 12529845376450, 12472148255347, 5199841084784, 673744214322, 16872920140, 0, 0] := by
  rw [show A10K2.u3618 = KTree.node A10K2.u3614 (nat_lit 59369235) (nat_lit 10787925433) (nat_lit 0) A10K2.u3617 from rfl, totK_node, atot3614, atot3617]
  decide +kernel

theorem arows3625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3625 = true := by
  rw [show A10K2.u3625 = KTree.node A10K2.u3621 (nat_lit 59398157) (nat_lit 5823242822) (nat_lit 0) A10K2.u3624 from rfl, allE_node, arows3621, irow3625, arows3624]
  all_goals rfl

theorem atot3625 : totK PA10K2 A10K2.u3625 = [0, 946272820892, 7017532881125, 15478465336403, 11977172339377, 2635417923347, 134189215387, 0, 0, 0] := by
  rw [show A10K2.u3625 = KTree.node A10K2.u3621 (nat_lit 59398157) (nat_lit 5823242822) (nat_lit 0) A10K2.u3624 from rfl, totK_node, atot3621, atot3624]
  decide +kernel

theorem arows3633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3633 = true := by
  rw [show A10K2.u3633 = KTree.node A10K2.u3629 (nat_lit 59455390) (nat_lit 14338232175) (nat_lit 0) A10K2.u3632 from rfl, allE_node, arows3629, irow3633, arows3632]
  all_goals rfl

theorem atot3633 : totK PA10K2 A10K2.u3633 = [0, 1609698614687, 8052851177131, 14797352994461, 11625166321160, 3451174599622, 357146288054, 6354482628, 0, 0] := by
  rw [show A10K2.u3633 = KTree.node A10K2.u3629 (nat_lit 59455390) (nat_lit 14338232175) (nat_lit 0) A10K2.u3632 from rfl, totK_node, atot3629, atot3632]
  decide +kernel

theorem arows3640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3640 = true := by
  rw [show A10K2.u3640 = KTree.node A10K2.u3636 (nat_lit 59502593) (nat_lit 10590452259) (nat_lit 0) A10K2.u3639 from rfl, allE_node, arows3636, irow3640, arows3639]
  all_goals rfl

theorem atot3640 : totK PA10K2 A10K2.u3640 = [0, 0, 2238807709339, 10589030830515, 16392573137387, 9200554746579, 1627156370528, 74702803208, 0, 0] := by
  rw [show A10K2.u3640 = KTree.node A10K2.u3636 (nat_lit 59502593) (nat_lit 10590452259) (nat_lit 0) A10K2.u3639 from rfl, totK_node, atot3636, atot3639]
  decide +kernel

end QECKChecks.A10K2
